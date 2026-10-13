"""count-catcher: reproduce the paper's results that run on one machine (4 cores, 14 GB; run by artifact/reproduce.sh).

    artifact/reproduce.sh --list
    artifact/reproduce.sh --all [--skip-large] [--jobs N] [--keep-files]
    artifact/reproduce.sh --stage NAME [NAME ...] [--skip-large] [--jobs N]

Stages run in the order of --list. Every item runs as a subprocess under artifact/measure.py
(wall time and peak memory of its process tree, sampled once a second), one item after the
other; its output goes to artifact/out/STAGE/ITEM.log. Each finished item appends a line to
artifact/out/results.tsv (stage, item, status, value, expected, wall s, peak MiB, paper
reference); a rerun of a stage replaces that stage's lines (with --item only the lines of those
items), and the lines of the other stages stay, so results.tsv accumulates over invocations. At
the end artifact/check.py compares results.tsv with artifact/expected.tsv and prints a PASS/FAIL
table for the stages of this invocation; with --item, the items not selected are NOTRUN, not
FAIL. The exit status is check.py's (1 on any FAIL).

  --jobs N      parallelism inside an item: -j of the graph drivers (triangle-free graphs,
                Ramsey graph) and the parallel tasks of the differential-test sample
                (default: the number of CPUs, at most 4)
  --skip-large  leave out the two showcases that need more than 10 GB (A358391(6), 13.4 GB in
                the paper's run; A303210(9), 11.8 GB)
  --keep-files  keep certificates, node tables and LRAT files (default: files above 20 MB are
                deleted when an item ends)

Peak memory is the peak of the summed proportional set sizes (PSS) of the item's processes:
memory-mapped files shared by several processes (Mathlib's .olean files) count once. It
includes the about 3 GB of Mathlib that every Lean process maps.
Standard library only; needs the installation of artifact/install.sh (or the prebuilt tree).
"""

import argparse
import concurrent.futures as cf
import gzip
import hashlib
import importlib.util
import os
import platform
import re
import resource
import shutil
import statistics
import subprocess
import sys
import textwrap
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ART = ROOT / "artifact"
OUT = ART / "out"
RESULTS = OUT / "results.tsv"
EXPECTED = ART / "expected.tsv"
LEAN = ROOT / "lean"
TOOLS = ROOT / "tools" / "bin"
SCRIPTS = ROOT / "scripts"
CC_BIN = ROOT / "bin" / "count-catcher"
AUDIT_DIR = ROOT / "research/eval-2026-10-07/contract_audit"
AUDIT_MAIN = AUDIT_DIR / "AuditMain.lean"
AUDIT_REF = AUDIT_DIR / "contract_lean_2026-10-11.txt"  # the records behind Table 11's column
LATIN8 = ROOT / "research/latin8-2026-10-04"  # the order-8 run: plan.json, res/<leaf>.txt
LATIN8_LEAF, LATIN8_LEAF_NAME = 653, "c6_0025"  # the leaf the artifact reruns (one of the smallest)
EXT = "dylib" if platform.system() == "Darwin" else "so"
PLUGINS = [
    f"--plugin={LEAN}/.lake/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.{EXT}",
    f"--plugin={LEAN}/.lake/build/lib/libCountCatcher_CountCatcherChecker.{EXT}",
]
UVRUN = ["uv", "run", "--no-project", "-q"]
COLS = ["stage", "item", "status", "value", "expected", "wall_s", "peak_MiB", "ref"]
ITEMIZED = {"tests", "showcases", "validation", "competition", "streamed"}  # stages --item selects in
BIG = 20 * 1000 * 1000  # files above this size are deleted after an item (unless --keep-files)

# Stages: name, what it reproduces, wall time and peak memory (PSS) of the stage in one run of
# --all at 4 CPUs and 14 GB in the clean Ubuntu 25.04 image on an Intel Xeon E5-2640 v4 machine
# (2026-10-08; the order-8 items measured there on 2026-10-11), and the wall time in the TACAS
# 2026 AE VM (4 vCPUs of an AMD EPYC 9274F host, 16 GB, offline, --all of the release on
# 2026-10-12; see the README, section on reproduce.sh).
STAGES = [
    ("tests", "the 37 end-to-end tests of lean/test (lean/test/run.sh, one test per item)",
     "3 min", "4.1 GiB", "2 min"),
    ("axioms", "#print axioms of the nine soundness theorems (Listing 5): only propext, "
     "Classical.choice, Quot.sound", "4 s", "3.3 GiB", "3 s"),
    ("handsuite", "the constructed certificates (Table 11, constructed column): 41 records "
     "through the audit driver and the 5 Lean-format cases of test/Adversarial.lean",
     "11 s", "3.6 GiB", "12 s"),
    ("showcases", "Table 3 without A396728(7): triangle-free graphs on 10 vertices, "
     "Latin squares of order 7 (the file of Listings 1 and 2), Dedekind M(7), A358391(6) "
     "[large], A303210(9) [large], A303210(10), the (3,5)-Ramsey graph on 13 vertices; "
     "order 8: latin8_all from the 737 leaf counts as hypotheses, and one leaf rerun",
     "73 min", "13.0 GiB", "47 min"),
    ("validation", "nine of the eleven validation instances (Table 7) through bin/count-catcher "
     "with the family lemmas", "46 min", "8.4 GiB", "32 min"),
    ("competition", "the 44 competition formulas with certificates below 100 MB "
     "(Table 10; count-catcher NAME --dimacs FILE --run)", "25 min", "4.1 GiB", "13 min"),
    ("streamed", "embedded against streamed refutation on 11 instances (Table 14): three theorem "
     "files per instance, three rounds", "15 min", "5.7 GiB", "10 min"),
    ("difftest", "a seeded sample of the differential test (Table 11, generated column; "
     "Section 4.5): each formula kept with all its mutants with probability 100,000 / 12,143,324, "
     "so about 100,000 records are expected; seed 1 gives 98,893", "4 min", "1.8 GiB", "5 min"),
    ("extras", "cpog-check's wrong count on random cubic 100 (Section A.5), the kernel-only check "
     "of the 4x4 domino refutation (Section 6), every number and table of the paper "
     "regenerated from the shipped logs by scripts/paper_numbers.py (incl. Table 12, lines of "
     "code)", "1.5 min", "6.4 GiB", "1 min"),
]
# measured totals: one job each on the Xeon, --all and --skip-large (2026-10-08, the version of
# that date, without the two order-8 items, which add about 3.5 min there), and --all of the
# release in the AE VM (2026-10-12; --skip-large not run there as a whole)
TOTAL = ("2 h 44 min", "13.0 GiB", "2 h 17 min", "9.5 GiB", "1 h 51 min")
LOG_ONLY = """\
Results that ship as logs only (Zenodo record, logs/; result files under research/):
  - CPOG 1.2.0's verified checker depends on two unproved lemmas (Section 4.5): needs CPOG's
    own Lean v4.4.0-rc1 toolchain and a Mathlib of 2024; the two proofs, the axiom report and
    the counterexample to the false lemma are in research/upstream/
  - ganak and SharpSAT-TD agree on the four OEIS values and the five graphs (Sections 6, A.3):
    the counters are not shipped; artifact/xcheck/ pins their commits and holds their outputs
    and a script that reruns both (xcheck.sh)
  - the reverse-check methods of Table 5 (top-down, per clause): lean/PartcMain.lean (lake build
    count-catcher-partc), lean/CountCatcherChecker/RevTD.lean, Rev.lean; timings in
    research/eval-2026-10-01/partc_topdown_table.tsv
  - Latin squares of order 8, all 737 leaves (7.9 TB of certificates; the showcases stage
    checks the assembly from the leaf counts and reruns one leaf), A396728(7) (18.2 GB of
    Lean memory), queens 14, the 16x16 grid, the full competition funnel (Tables 8 and 9), the
    comparison with CPOG's checkers (Figure 3, Table 4), the ablations of Table 5 and the unshortened
    refutation, the full differential test (12.1 million certificates); the extras stage
    regenerates all their numbers and tables from these logs"""


# ---------------------------------------------------------------- helpers

def safe(name):
    return re.sub(r"[^A-Za-z0-9_.+-]", "_", name)


def env_path():
    env = dict(os.environ)
    env["PATH"] = os.pathsep.join([str(ROOT / "bin"), str(TOOLS), env.get("PATH", "")])
    return env


def read_kv(path):
    d = {}
    try:
        with open(path, errors="replace") as f:
            for line in f:
                if "=" in line:
                    k, v = line.rstrip("\n").split("=", 1)
                    d[k] = v
    except OSError:
        pass
    return d


def text(path):
    try:
        return Path(path).read_text(errors="replace")
    except OSError:
        return ""


def load_expected():
    exp = {}
    if EXPECTED.exists():
        lines = EXPECTED.read_text().splitlines()
        hdr = lines[0].split("\t")
        for line in lines[1:]:
            if not line.strip() or line.startswith("#"):
                continue
            r = dict(zip(hdr, line.split("\t")))
            exp[(r["stage"], r["item"])] = r
    return exp


def cleanup(*dirs):
    """Delete files above BIG bytes below dirs (certificates, LRAT, node tables, .olean)."""
    for d in dirs:
        for p in Path(d).rglob("*") if Path(d).exists() else []:
            try:
                if p.is_file() and not p.is_symlink() and p.stat().st_size > BIG:
                    p.unlink()
            except OSError:
                pass


class Run:
    """One invocation: the stages to run, the results file, the measured items."""

    def __init__(self, a):
        self.a = a
        self.jobs = a.jobs
        self.exp = load_expected()
        self.rows = []  # rows of the stages not rerun (kept), then the new ones
        if RESULTS.exists():
            lines = RESULTS.read_text().splitlines()
            for line in lines[1:]:
                r = line.split("\t")
                if r and not (r[0] in a.stages and (r[0] not in ITEMIZED or self.want(r[1].split(" ")[0]))):
                    self.rows.append(r)
        self.env = env_path()

    def want(self, key):
        """Whether item KEY runs (--item restricts the items of the stages; default all)."""
        return not self.a.item or key in self.a.item

    def add(self, stage, item, status, value, wall="-", peak="-"):
        e = self.exp.get((stage, item), {})
        value = str(value).replace("\t", " ").replace("\n", " ")
        row = [stage, item, status, value, e.get("expected", "-"), str(wall), str(peak),
               e.get("ref", "-")]
        self.rows.append(row)
        OUT.mkdir(parents=True, exist_ok=True)
        tmp = RESULTS.with_suffix(".tmp")
        tmp.write_text("\t".join(COLS) + "\n" + "".join("\t".join(r) + "\n" for r in self.rows))
        tmp.replace(RESULTS)
        short = value if len(value) <= 40 else value[:37] + "..."
        print(f"  {stage:<11} {item:<34} {status:<6} {short:<40} {wall:>6} s {peak:>7} MiB",
              flush=True)

    def measure(self, stage, item, cmd, cwd, env=None, log=None):
        """Run cmd under measure.py; return (exit code, wall s, peak PSS MiB, log path)."""
        d = OUT / stage
        d.mkdir(parents=True, exist_ok=True)
        log = Path(log) if log else d / f"{safe(item)}.log"
        log.write_text("")
        stats = d / "stats.tsv"
        cmd = [sys.executable, str(ART / "measure.py"), item, str(log), str(stats), "--",
               *map(str, cmd)]
        rc = subprocess.run(cmd, cwd=cwd, env=env or self.env).returncode
        wall = peak = "-"
        try:
            last = stats.read_text().splitlines()[-1].split("\t")
            if last[0] == item:
                wall, peak = last[2], last[3]
        except (OSError, IndexError):
            pass
        return rc, wall, peak, log

    def internal(self, stage, item, *args):
        """Run a sub-procedure of this script (--internal) as a measured item."""
        return self.measure(stage, item, [sys.executable, __file__, "--internal", *args], ROOT)


def status_of(rc, ok):
    if rc == 137 or rc == -9:
        return "killed"
    return "ok" if ok else "fail"


def cc_count(log, name):
    m = re.search(rf"^count-catcher: theorem {re.escape(name)} proved, count (\d+)", text(log), re.M)
    return m.group(1) if m else None


# ---------------------------------------------------------------- stages

def st_tests(r):
    names = sorted(p.stem for p in (LEAN / "test").glob("*.lean"))
    for n in filter(r.want, names):
        rc, wall, peak, log = r.measure("tests", n, [LEAN / "test/run.sh", n], LEAN)
        m = re.search(rf"^(PASS|FAIL|DIFF|NOEXP|MISSING)\s+{re.escape(n)}\b", text(log), re.M)
        v = m.group(1) if m else "no result"
        r.add("tests", n, status_of(rc, rc == 0 and v == "PASS"), v, wall, peak)


AXIOM_THEOREMS = [
    "CountCatcher.checkPog_sound", "CountCatcher.fwd_of_unsat",
    "CountCatcher.checkRevKillFast_sound", "CountCatcher.card_models_eq_countRoot",
    "CountCatcher.checkAll_sound", "CountCatcher.checkAllAC_sound",
    "CountCatcher.fwdCnfOf_unsat_of_sel", "LRATCatcher.checkStreamCnf_sound",
    "CountCatcher.Family.card_of_checkAC",
]


def axioms_of(txt):
    """{theorem: 'ax1,ax2,...'} from #print axioms output (lists may span lines)."""
    out = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", txt):
        out[m.group(1)] = ",".join(x.strip() for x in m.group(2).split(","))
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", txt):
        out[m.group(1)] = "none"
    return out


def st_axioms(r):
    rc, wall, peak, log = r.measure("axioms", "Axioms.lean",
                                    ["lake", "env", "lean", ART / "Axioms.lean"], LEAN)
    r.add("axioms", "Axioms.lean", status_of(rc, rc == 0), f"exit {rc}", wall, peak)
    found = axioms_of(text(log))
    for t in AXIOM_THEOREMS:
        r.add("axioms", t, "ok" if t in found else "fail", found.get(t, "missing"))


# Table 11's rows (check, stages of the audit driver) as in scripts/paper_numbers.py, and the
# Lean-format cases of test/Adversarial.lean by their report
ADV_ROWS = [["cnf-wf"], ["pog-V"], ["A-arg"], ["A-prod-overlap"], ["A-sum-hint-ref"], ["A-sum-rup"],
            ["A-root-range"], ["C-negation"], ["C-clause"], ["B-parse"], ["B"]]
ADV_REPORT_STAGE = [("does not follow by strict RUP", "A-sum-rup"),
                    ("does not cite a defining clause", "A-sum-hint-ref"),
                    ("is not an earlier variable", "A-arg")]


def adv_records(txt):
    """[(record, verdict, stage)] of an audit driver output, stages as in Table 11."""
    out = []
    for m in re.finditer(r"^R (\S+) (ACCEPT|REJECT) stage=(\S+)", txt, re.M):
        st = re.sub(r"-node\d+", "", m.group(3))
        st = re.sub(r"^(C-clause|pog-V)\d+$", r"\1", st)
        out.append((m.group(1), m.group(2), {"B-check": "B"}.get(st, st)))
    return out


def adv_column(txt):
    """Table 11's constructed column for the records of txt plus the Lean-format cases:
    'n1 n2 ... n11; accepted A; total T' and the per-stage counts."""
    st = {}
    recs = adv_records(txt)
    for _, v, s in recs:
        st[s if v == "REJECT" else "accepted"] = st.get(s if v == "REJECT" else "accepted", 0) + 1
    adv = re.findall(r'info: some\s+"([^"]*)"\s*-/\s*#guard_msgs in\s*#eval reportA',
                     text(LEAN / "test/Adversarial.lean"))
    for msg in adv:
        s = next((x for k, x in ADV_REPORT_STAGE if k in msg), "unclassified")
        st[s] = st.get(s, 0) + 1
    col = " ".join(str(sum(st.get(x, 0) for x in row)) for row in ADV_ROWS)
    return f"{col}; accepted {st.get('accepted', 0)}; total {len(recs) + len(adv)}", st


def st_handsuite(r):
    d = OUT / "handsuite"
    cases = d / "cases"
    shutil.rmtree(cases, ignore_errors=True)
    cc = ROOT / "research/eval-2026-09-30/contract_audit/contract_cases.py"
    rc, wall, peak, log = r.measure("handsuite", "contract_cases",
                                    [*UVRUN, cc, cases, TOOLS, LEAN / "test/adversarial"], ROOT)
    bundle = cases / "contract.bundle"
    n = text(bundle).count("@inst ")
    r.add("handsuite", "contract_cases", status_of(rc, rc == 0 and n > 0), n, wall, peak)
    tmp = d / "tmp"
    tmp.mkdir(parents=True, exist_ok=True)
    rc, wall, peak, log = r.measure("handsuite", "audit",
                                    ["lake", "env", "lean", *PLUGINS, "--run", AUDIT_MAIN,
                                     bundle, tmp], LEAN)
    out = text(log)
    got = {l.split()[1]: l.strip() for l in out.splitlines() if l.startswith("R ")}
    ref = {l.split()[1]: l.strip() for l in text(AUDIT_REF).splitlines() if l.startswith("R ")}
    same = sum(1 for k, v in ref.items() if got.get(k) == v)
    diff = [f"expected: {v}\n     got: {got.get(k, '(missing)')}" for k, v in ref.items()
            if got.get(k) != v] + [f"extra: {v}" for k, v in got.items() if k not in ref]
    (d / "audit_diff.txt").write_text("\n".join(diff) + "\n")
    m = re.search(r"^SUMMARY \S+ (.*)$", out, re.M)
    # the driver exits 1 because of c24's STREAMDIFF flag (the known one, see difftest_rerun.md)
    r.add("handsuite", "audit verdicts", status_of(rc, m is not None),
          f"{same} of {len(ref)} identical" + (f", {len(diff)} differ (audit_diff.txt)" if diff else ""),
          wall, peak)
    r.add("handsuite", "audit summary", "ok" if m else "fail", m.group(1) if m else "no SUMMARY line")
    # the constructed column of Table 11 (rows in the table's order, then accepted and total):
    # these records plus the Lean-format cases of test/Adversarial.lean
    r.add("handsuite", "constructed column", "ok" if got else "fail", adv_column(text(log))[0])
    rc, wall, peak, log = r.measure("handsuite", "Adversarial.lean",
                                    [LEAN / "test/run.sh", "Adversarial"], LEAN)
    m = re.search(r"^(PASS|FAIL|DIFF|NOEXP)\s+Adversarial\b", text(log), re.M)
    v = m.group(1) if m else "no result"
    r.add("handsuite", "Adversarial.lean", status_of(rc, v == "PASS"), v, wall, peak)


def st_showcases(r):
    d = OUT / "showcases"
    j = str(r.jobs)

    def common(o, w):
        return ["--out", o, "--work", w, "--lean", LEAN, "--tools", TOOLS]

    items = [  # key, large, command(out, work); as scripts/cluster/rerun_showcase.sbatch ran them
        ("tri10", False, lambda o, w: [*UVRUN, SCRIPTS / "graph_orbits.py", "--family", "clique:3",
                                       "--n", "10", *common(o, w), "-j", j, "--inline"]),
        # one theorem file with the listing's names (latin7_fibre0 to 3, latin7_reduced,
        # latin7_all) and relative paths ("c0/fwd.pog"); each fibre by bin/count-catcher
        ("lat7", False, lambda o, w: [*UVRUN, SCRIPTS / "showcase/latin_cycles.py", "--n", "7",
                                      "--out", o, "--single"]),
        # order 8: latin8_all from the 737 leaf counts as hypotheses (no certificate), and the
        # rerun of one leaf certificate (c6_0025) end to end
        ("lat8asm", False, lambda o, w: [*UVRUN, SCRIPTS / "showcase/latin_cycles.py", "--plan",
                                         LATIN8 / "plan.json", "--assemble-hyp", "--hyp-out",
                                         o / "latin8_all.lean", "--lean", LEAN]),
        ("lat8leaf", False, lambda o, w: [*UVRUN, SCRIPTS / "showcase/latin_cycles.py", "--plan",
                                          LATIN8 / "plan.json", "--leaf", str(LATIN8_LEAF),
                                          "--out", o, "--scratch", w, "--lean", LEAN,
                                          "--tools", TOOLS]),
        ("ded7", False, lambda o, w: [*UVRUN, SCRIPTS / "showcase/dedekind.py", "--n", "7",
                                      *common(o, w)]),
        # the command of the paper's listing (the paper's run used scripts/showcase/kreweras.py)
        ("krew6", True, lambda o, w: [CC_BIN, "kreweras6", "--via",
                                      "Kreweras.card_of_check (n := 6)", "--run", "--dir", o]),
        ("td9", True, lambda o, w: [*UVRUN, SCRIPTS / "showcase/a303210.py", "--n", "9",
                                    *common(o, w)]),
        ("td10", False, lambda o, w: [*UVRUN, SCRIPTS / "showcase/a303210.py", "--n", "10",
                                      *common(o, w)]),
        ("r35_13", False, lambda o, w: [*UVRUN, SCRIPTS / "graph_orbits.py", "--family",
                                        "ramsey:3:5", "--n", "13", "--split", "--witness",
                                        "(circulantGraph ({1, 5} : Set (Fin 13)))",
                                        *common(o, w), "-j", j, "--inline"]),
    ]
    for key, large, cmd in filter(lambda x: r.want(x[0]), items):
        o, w = d / key, d / key / "work"
        if large and r.a.skip_large:
            r.add("showcases", key, "skip", "--skip-large")
            continue
        shutil.rmtree(o, ignore_errors=True)
        o.mkdir(parents=True)
        rc, wall, peak, log = r.measure("showcases", key, cmd(o, w), o)
        res = read_kv(o / "result.txt")
        if key == "tri10" or key == "r35_13":
            ok = res.get("status") == "proved"
            r.add("showcases", key, status_of(rc, ok), res.get("orbits", "-"), wall, peak)
            if key == "tri10":
                r.add("showcases", "tri10 labelled", "ok" if ok else "fail", res.get("labelled", "-"))
            else:
                proved = "'ramsey35_13_unique' depends on axioms" in text(o / "lean.out")
                r.add("showcases", "r35_13 unique", "ok" if proved else "fail",
                      "proved" if proved else "not proved")
        elif key == "lat7":
            asm = read_kv(o / "assemble.txt")
            ok = asm.get("status") == "proved"
            r.add("showcases", key, status_of(rc, ok), asm.get("count", "-"), wall, peak)
            thy = text(o / "latin7.lean")
            m = re.search(r"theorem latin7_all :\s*Nat\.card \{L : Fin 7 → Fin 7 → Fin 7 // "
                          r"IsLatin L\} = (\d+)", thy)
            named = "'latin7_all' depends on axioms" in text(o / "lean.out")
            r.add("showcases", "lat7 all", "ok" if ok and m and named else "fail",
                  m.group(1) if m else "-")
            r.add("showcases", "lat7 axioms", "ok" if ok else "fail",
                  f"native={asm.get('axioms_native', '-')} sorry={asm.get('axioms_sorry', '-')}")
            # the listing's names and paths: count_models latin7_fibreI ... "cI/fwd.pog"
            # "cI/fwd.lrat" (keep := "cI/fwd.keep"), then latin7_reduced and latin7_all
            fib = re.findall(r'^count_models (latin7_fibre\d)\n  via \(Latin\.fibre_card_of_check '
                             r'\(n := 7\) \(r := ![^)]*\)\)\n  "(c\d)/fwd\.pog" "\2/fwd\.lrat" '
                             r'\(keep := "\2/fwd\.keep"\) \(count := \d+\)$', thy, re.M)
            thms = re.findall(r"^theorem (\S+) :", thy, re.M)
            v = (f"{' '.join(f for f, _ in fib)} with keep mask, paths {' '.join(c for _, c in fib)}; "
                 f"theorems {' '.join(thms)}")
            r.add("showcases", "lat7 file", "ok" if ok and len(fib) == 4 else "fail", v)
        elif key == "lat8asm":
            res = read_kv(o / "latin8_all.txt")
            thy = text(o / "latin8_all.lean")
            ok = res.get("status") == "proved"
            m = re.search(r"IsLatin L\} = (\d+)", thy)
            r.add("showcases", key, status_of(rc, ok), m.group(1) if ok and m else "-", wall, peak)
            ax = axioms_of(text(o / "latin8_all.out")).get("latin8_all", "missing")
            r.add("showcases", "lat8asm axioms", "ok" if ok else "fail", ax)
            hyps = len(re.findall(r"^    \(h\d : latin8_leaves ", thy.split("theorem latin8_all")[-1], re.M))
            r.add("showcases", "lat8asm hypotheses", "ok" if ok else "fail",
                  f"{hyps} hypotheses over {res.get('leaves', '-')} leaf counts")
            same = thy == text(ART / "latin8_all.lean")
            r.add("showcases", "lat8asm file", "ok" if thy else "fail",
                  "identical to artifact/latin8_all.lean" if same else "differs from artifact/latin8_all.lean")
        elif key == "lat8leaf":
            P = read_kv(LATIN8 / "res" / f"{LATIN8_LEAF_NAME}.txt")
            res = read_kv(o / "res" / f"{LATIN8_LEAF_NAME}.txt")
            ok = res.get("status") == "proved"
            r.add("showcases", key, status_of(rc, ok), res.get("count_lean", "-"), wall, peak)
            lo = text(o / "res" / f"{LATIN8_LEAF_NAME}.lean.out")
            thm = f"latin8_{LATIN8_LEAF_NAME}"
            r.add("showcases", "lat8leaf theorem", "ok" if ok else "fail",
                  f"{thm} proved, as in research/latin8-2026-10-04/res (count {P.get('count_lean')})"
                  if ok and f"'{thm}' depends on axioms" in lo and res.get("count_lean") == P.get("count_lean")
                  else f"differs: {res.get('count_lean')} against {P.get('count_lean')}")
        elif key == "krew6":
            c = cc_count(log, "kreweras6")
            r.add("showcases", key, status_of(rc, c is not None), c or "-", wall, peak)
        else:
            ok = res.get("status") == "proved"
            r.add("showcases", key, status_of(rc, ok), res.get("count", "-"), wall, peak)
        if not r.a.keep_files:
            shutil.rmtree(w, ignore_errors=True)
            cleanup(o)


def gen_graph(outdir, name, spec):
    """Write NAME.cnf and NAME.edges with scripts/gen_t5.py; spec as in its usage."""
    outdir.mkdir(parents=True, exist_ok=True)
    subprocess.run([*UVRUN, SCRIPTS / "gen_t5.py", outdir, name, *spec], check=True,
                   stdout=subprocess.DEVNULL, env=env_path())
    return outdir / f"{name}.cnf", outdir / f"{name}.edges"


GRAPHS = {  # instance: arguments of scripts/gen_t5.py after OUTDIR NAME
    "cub100": ["cubic", "100", "1"],
    "cub120": ["cubic", "120", "1"],
    "games120": ["col", str(ART / "inputs/graphs/games120.col")],
    "homer": ["col", str(ART / "inputs/graphs/homer.col")],
    "hq6": ["hypercube", "6"],
}


def edge_via(edges_path, k):
    es = [tuple(map(int, l.split())) for l in open(edges_path) if l.strip()]
    lits = ", ".join(f"s({u}, {v})" for u, v in es)
    return f"edgeGraph_card_of_check (k := {k}) (l := [{lits}])"


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def st_validation(r):
    d = OUT / "validation"
    g = d / "graphs"
    shutil.rmtree(g, ignore_errors=True)
    inst = [
        ("dom12", "domino_12x12", "Domino.card_of_check (R := 12) (C := 12)"),
        ("q12", "queens12", "Queens.card_of_check (n := 12)"),
        ("q13", "queens13", "Queens.card_of_check (n := 13)"),
        ("ind14", "grid14_indepSets", "grid_card_of_check (n := 14)"),
        ("hq6", "hypercube6_indepSets", "hypercube_card_of_check (n := 6)"),
    ]
    # the four graphs given by edge lists: regenerated by gen_t5.py (cubic graphs: seed 1;
    # games120, homer: the DIMACS coloring files in artifact/inputs/graphs); the row "graph
    # inputs" holds the sha256 prefix of each edge list (the .cnf has the input path in a comment)
    same = []
    for name in ("cub100", "cub120", "games120", "homer"):
        cnf, edges = gen_graph(g, name, GRAPHS[name])
        k = int(next(l.split()[2] for l in open(cnf) if l.startswith("p cnf")))
        inst.append((name, f"{name}_indepSets", edge_via(edges, k)))
        same.append(f"{name}:{sha256(edges)[:16]}")
    if not r.a.item:
        r.add("validation", "graph inputs", "ok", " ".join(same))
    for key, thm, via in filter(lambda x: r.want(x[0]), inst):
        o = d / key
        shutil.rmtree(o, ignore_errors=True)
        o.mkdir(parents=True)
        rc, wall, peak, log = r.measure("validation", key,
                                        [CC_BIN, thm, "--via", via, "--run", "--dir", o], d)
        c = cc_count(log, thm)
        r.add("validation", key, status_of(rc, c is not None), c or "-", wall, peak)
        if not r.a.keep_files:
            cleanup(o)


def st_competition(r):
    d = OUT / "competition"
    src = ROOT / "inputs/mc2022_subset"
    lst = ROOT / "inputs/mc2022_subset.sha256"
    good = total = 0
    bad = []
    for line in text(lst).splitlines():
        if not line.strip():
            continue
        h, name = line.split()
        total += 1
        p = src / name.lstrip("*")
        if p.exists() and sha256(p) == h:
            good += 1
        else:
            bad.append(name)
    if not r.a.item:
        r.add("competition", "sha256", "ok" if good == total and total else "fail",
              f"{good} of {total} match" + (f" (bad: {' '.join(bad)})" if bad else ""))
    for cnf in sorted(src.glob("*.cnf")):
        name = cnf.stem
        if not r.want(name):
            continue
        o = d / name
        shutil.rmtree(o, ignore_errors=True)
        o.mkdir(parents=True)
        rc, wall, peak, log = r.measure("competition", name,
                                        [CC_BIN, name, "--dimacs", cnf, "--run", "--dir", o], d)
        c = cc_count(log, name)
        r.add("competition", name, status_of(rc, c is not None), c or "-", wall, peak)
        if not r.a.keep_files:
            cleanup(o)


# Embedded against streamed (measurement 2 of research/eval-2026-10-04/embedded_streamed.md,
# its job script m2.sbatch ported): instance, family, argument, CNF source, doc line.
STREAMED = [
    ("cub100", "edges", "-", ("graph", "cub100"),
     "cub100: random cubic graph on 100 vertices from scripts/gen_t5.py with seed 1"),
    ("dom08", "domino", "8", ("gen_domino.py", "8"), None),
    ("dom10", "domino", "10", ("gen_domino.py", "10"), None),
    ("homer", "edges", "-", ("graph", "homer"), "homer: DIMACS coloring benchmark"),
    ("hq6", "hypercube", "6", ("graph", "hq6"), None),
    ("ind10", "grid", "10", ("gen_indep.py", "10"), None),
    ("ind12", "grid", "12", ("gen_indep.py", "12"), None),
    ("mc2022_track1_011", "dimacs", "-", ("file", "mc2022_track1_011"), "mc2022_track1_011"),
    ("mc2022_track2_007", "dimacs", "-", ("file", "mc2022_track2_007"), "mc2022_track2_007"),
    ("q10", "queens", "10", ("gen_queens.py", "10"), None),
    ("q11", "queens", "11", ("gen_queens.py", "11"), None),
]
REPS = 3


def st_streamed(r):
    ratios = {"S1": [], "S2": []}
    for inst, *_ in STREAMED:
        if not r.want(inst):
            continue
        rc, wall, peak, log = r.internal("streamed", inst, "streamed", inst)
        res = read_kv(OUT / "streamed" / inst / "result.txt")
        ok = res.get("status") == "done"
        r.add("streamed", inst, status_of(rc, ok), res.get("count", "-"), wall, peak)
        for s in ("S1", "S2"):
            v = res.get(f"E/{s}_check")
            if v and v != "NA":
                ratios[s].append(float(v))
            r.add("streamed", f"{inst} E/{s}", "ok" if v and v != "NA" else "fail", v or "-")
        if not r.a.keep_files:
            cleanup(OUT / "streamed" / inst)
    for s in ("S1", "S2"):
        v = ratios[s]
        if r.a.item:
            break
        r.add("streamed", f"median E/{s}", "ok" if v else "fail",
              f"{statistics.median(v):.3f}" if v else "-")


def st_difftest(r):
    rc, wall, peak, log = r.internal("difftest", "sample", "difftest")
    d = OUT / "difftest"
    summ = text(d / "summary.txt")
    m = re.search(r"Lean records \(without controls\): (\d+), controls: (\d+)", summ)
    r.add("difftest", "records", status_of(rc, m is not None), m.group(1) if m else "-", wall, peak)
    mc = re.search(r"^## Positive controls: (\d+): (.*)$", summ, re.M)
    if mc:
        ok_ctl = sum(int(x) for x in re.findall(r"CONTROL-OK (\d+)", mc.group(2)))
        v = f"{ok_ctl} of {mc.group(1)} CONTROL-OK"
    else:
        v = "-"
    r.add("difftest", "controls", "ok" if mc else "fail", v)
    mf = re.search(r"^## Flagged records \([^)]*\): (\d+)", summ, re.M)
    r.add("difftest", "flagged", "ok" if mf else "fail", mf.group(1) if mf else "-")
    ma = re.search(r"^  all: ([\d,]+) records, ([\d,]+) accepted", summ, re.M)
    r.add("difftest", "accepted", "ok" if ma else "fail", ma.group(2).replace(",", "") if ma else "-")
    ref = text(ROOT / "research/eval-2026-10-07/difftest_sample_kinds.tsv")
    got = text(d / "kinds.tsv")
    if got and got == ref:
        v = "identical"
    elif got:
        rl, gl = ref.splitlines(), got.splitlines()
        v = f"{sum(1 for x in gl if x in set(rl))} of {len(rl)} lines identical"
    else:
        v = "missing"
    r.add("difftest", "kinds table", "ok" if got else "fail", v)


def st_extras(r):
    d = OUT / "extras"
    # cpog-check's wrong count (Section A.5, smallest case)
    rc, wall, peak, log = r.internal("extras", "cub100 cpog-check", "k19")
    res = read_kv(d / "k19" / "result.txt")
    ok = res.get("status") == "done"
    r.add("extras", "cub100 cpog-check count", status_of(rc, ok), res.get("cc_count", "-"), wall, peak)
    r.add("extras", "cub100 cpog-check success", "ok" if ok else "fail", res.get("cc_success", "-"))
    r.add("extras", "cub100 D4 count", "ok" if ok else "fail", res.get("d4_count", "-"))
    # kernel-only check of the masked 4x4 domino refutation
    rc0, _, _, _ = r.internal("extras", "dom4 certificate", "k26prep")
    k = d / "k26"
    res = read_kv(k / "result.txt")
    r.add("extras", "dom4 refutation size", "ok" if rc0 == 0 else "fail",
          f"{res.get('clauses', '-')} clauses, {res.get('additions', '-')} additions")
    for mode, extra in (("kernel", []), ("native", PLUGINS)):
        f = k / f"{mode}.lean"
        rc, wall, peak, log = r.measure("extras", f"dom4 {mode}",
                                        ["lake", "env", "lean", *extra, f], LEAN)
        ax = axioms_of(text(log)).get("dom4_fwd_ki", "missing")
        st = re.findall(r"^stamp (\d+)", text(log), re.M)
        cmd_ms = int(st[1]) - int(st[0]) if len(st) >= 2 else None
        r.add("extras", f"dom4 {mode}", status_of(rc, rc == 0 and ax != "missing"), ax, wall, peak)
        r.add("extras", f"dom4 {mode} command ms", "ok" if cmd_ms is not None else "fail",
              cmd_ms if cmd_ms is not None else "-")
    # every number and table of the paper from the shipped logs
    rc, wall, peak, log = r.internal("extras", "paper_numbers.py", "paper")
    res = read_kv(d / "paper" / "compare.txt")
    r.add("extras", "paper_numbers.py", status_of(rc, rc == 0), f"exit {rc}", wall, peak)
    for k2 in sorted(res):
        r.add("extras", k2, "ok" if rc == 0 else "fail", res[k2])


STAGE_FN = {"tests": st_tests, "axioms": st_axioms, "handsuite": st_handsuite,
            "showcases": st_showcases, "validation": st_validation,
            "competition": st_competition, "streamed": st_streamed, "difftest": st_difftest,
            "extras": st_extras}


# ---------------------------------------------------------------- sub-procedures (--internal)

def sh(cmd, cwd, out=None, env=None):
    """Run cmd; output to file out (or discarded); return (exit code, wall s, peak RSS kB)."""
    t = time.time()
    with open(out, "w") if out else open(os.devnull, "w") as f:
        p = subprocess.Popen([str(x) for x in cmd], cwd=cwd, stdout=f, stderr=subprocess.STDOUT,
                             env=env or env_path())
        _, status, ru = os.wait4(p.pid, 0)
    rc = os.waitstatus_to_exitcode(status)
    return rc, time.time() - t, ru.ru_maxrss


def check_ms(out):
    m = re.search(r"\(parts A, B, C\) (\d+) ms", out)
    if m:
        return int(m.group(1))
    b = re.search(r"part B[^,]* (\d+) ms", out)
    ac = re.search(r"parts A and C (\d+) ms", out)
    return int(b.group(1)) + int(ac.group(1)) if b and ac else None


def in_streamed(inst):
    fam, arg, src, desc = next((f, a, s, dd) for i, f, a, s, dd in STREAMED if i == inst)
    w = OUT / "streamed" / inst
    shutil.rmtree(w, ignore_errors=True)
    w.mkdir(parents=True)
    res = w / "result.txt"
    lines = []

    def kv(k, v):
        lines.append(f"{k}={v}")
        res.write_text("\n".join(lines) + "\n")

    kv("inst", inst)
    kv("family", f"{fam} {arg}")
    cnf = w / "in.cnf"
    if src[0] == "graph":
        c, e = gen_graph(w, inst, GRAPHS[src[1]])
        shutil.copy(c, cnf)
    elif src[0] == "file":
        shutil.copy(ROOT / "inputs/mc2022_subset" / f"{src[1]}.cnf", cnf)
        shutil.copy(cnf, w / f"{inst}.cnf")  # the file the theorem names, next to it
    else:
        with open(cnf, "w") as f:
            subprocess.run([*UVRUN, SCRIPTS / src[0], src[1]], stdout=f, check=True, env=env_path())
    kv("cnf_hdr", next(l.strip() for l in open(cnf) if l.startswith("p")))
    e, t, _ = sh(["d4", "in.cnf", "-dDNNF", "-out=in.nnf"], w, w / "d4.log")
    kv("d4_exit", e), kv("d4_s", f"{t:.1f}")
    m = re.search(r"^s (\d+)", text(w / "d4.log"), re.M)
    n = m.group(1) if m else "-"
    kv("d4_count", n)
    e, t, _ = sh(["cpog-gen-fwd", "-F", "-T", "500", "-G", "in.cnf", "in.nnf", "cert.cpog"], w, w / "gen.log")
    kv("gen_exit", e), kv("gen_s", f"{t:.1f}")
    e1, t, _ = sh(["cpog2lrat", "in.cnf", "cert.cpog", "emb", "--delete", "--trim"], w, w / "c2l_emb.log")
    kv("c2l_emb_exit", e1), kv("c2l_emb_s", f"{t:.1f}")
    e2, t, _ = sh(["cpog2lrat", "in.cnf", "cert.cpog", "str", "--delete", "--binary", "--trim",
                   "--keep", "--inline"], w, w / "c2l_str.log")
    kv("c2l_str_exit", e2), kv("c2l_str_s", f"{t:.1f}")
    for x in ("in.nnf", "cert.cpog", "emb.cnf", "str.cnf"):
        (w / x).unlink(missing_ok=True)
    if e1 or e2 or n == "-":
        kv("status", "failed_before_lean")
        sys.exit(1)
    for x in ("emb.lrat", "str.lrat"):
        kv(f"{x.split('.')[0]}_lrat_bytes", (w / x).stat().st_size)
    ap = {"edges": str(w / f"{inst}.cnf"), "dimacs": str(w / f"{inst}.cnf")}.get(fam, arg)
    # theorem files in w with paths relative to it (count_models resolves them against the file)
    tl = [*UVRUN, SCRIPTS / "theorem_lean.py", "--command", "--base", w]
    dd = [desc or inst]
    files = {"E": [fam, ap, "embed", n, "emb.pog", "emb.lrat", *dd],
             "S1": [fam, ap, "stream", n, "emb.pog", "emb.lrat", *dd],
             "S2": ["--keep", str(w / "str.keep"), fam, ap, "stream", n, "str.pog", "str.lrat", *dd]}
    for k, a in files.items():
        e, _, _ = sh([*tl, *a], w, w / f"{k}.lean")
        kv(f"tl_{k}", e)
    (w / "warm.lean").write_text("import CountCatcher\n")

    def lean(tag, f):
        e, t, rss = sh(["lake", "env", "lean", *PLUGINS, w / f], LEAN, w / f"{tag}.out")
        out = text(w / f"{tag}.out")
        good = e == 0 and out.count("depends on axioms") == 1 and "error" not in out
        m = re.search(r"^count_models \S+: (\d+) models", out, re.M)
        kv(f"{tag}_exit", e), kv(f"{tag}_wall_s", f"{t:.2f}"), kv(f"{tag}_maxrss_kb", rss)
        kv(f"{tag}_ok", int(good and m is not None and m.group(1) == n))
        kv(f"{tag}_check_ms", check_ms(out))
        return good and m is not None and m.group(1) == n, check_ms(out)

    lean("warm", "warm.lean")
    order = ["E", "S1", "S2"]
    ms = {k: [] for k in order}
    allok = True
    for rep in range(1, REPS + 1):
        for i in range(3):
            k = order[(i + rep - 1) % 3]
            ok, c = lean(f"{k}_r{rep}", f"{k}.lean")
            allok &= ok
            if ok and c is not None:
                ms[k].append(c)
    med = {k: statistics.median(v) if v else None for k, v in ms.items()}
    for k in order:
        kv(f"{k}_check_ms_median", med[k])
    for s in ("S1", "S2"):
        kv(f"E/{s}_check", f"{med['E'] / med[s]:.3f}" if med["E"] and med[s] else "NA")
    kv("count", n if allok else "-")
    kv("status", "done" if allok else "lean_failed")
    sys.exit(0 if allok else 1)


def in_difftest():
    d = OUT / "difftest"
    shutil.rmtree(d / "results", ignore_errors=True)
    shutil.rmtree(d / "work", ignore_errors=True)
    tasks = [l.split() for l in text(AUDIT_DIR / "worklist_sample.txt").splitlines() if l.strip()]
    jobs = int(os.environ.get("CC_REPRO_JOBS", "4"))

    def task(i):
        st, shard, nsh, count, mut, sample = tasks[i]
        block = [1, 2, 3, 4096][i % 4]
        w = d / "work" / f"audit_{st}_{shard}"
        rd = d / "results" / f"{st}_{shard}"
        w.mkdir(parents=True)
        rd.mkdir(parents=True)
        info = rd / "info.txt"
        lines = [f"host={platform.node()} set={st} shard={shard}/{nsh} count={count} mut={mut} "
                 f"sample={sample} block={block} start={int(time.time())}"]
        e, t, rss = sh([sys.executable, AUDIT_DIR / "difftest.py", st, shard, nsh, w, "--tools", TOOLS,
                        "--count", count, "--mut", mut, "--seed", "1", "--plainsample", "0.05",
                        "--sample", sample], ROOT, w / "difftest.log")
        bb = (w / "bundle").stat().st_size if (w / "bundle").exists() else 0
        lines.append(f"difftest_exit={e} difftest_s={int(t)} bundle_bytes={bb} difftest_maxrss_kb={rss}")
        env = env_path()
        env["LRATCATCHER_STREAM_BLOCK"] = str(block)
        t1 = time.time()
        with open(w / "lean.out", "w") as fo, open(w / "lean.err", "w") as fe:
            p = subprocess.Popen(["lake", "env", "lean", *PLUGINS, "--run", str(AUDIT_MAIN),
                                  str(w / "bundle"), str(w)], cwd=LEAN, stdout=fo, stderr=fe, env=env)
            _, status, ru = os.wait4(p.pid, 0)
        e = os.waitstatus_to_exitcode(status)
        err = text(w / "lean.err")
        lines.append(f"lean_exit={e} lean_s={int(time.time() - t1)} lean_maxrss_kb={ru.ru_maxrss} "
                     f"lean_err_panics={err.count('index out of bounds')}")
        lo = text(w / "lean.out").splitlines()
        lines.append(lo[-1] if lo else "")
        lines.append(text(w / "difftest.log").rstrip("\n"))
        (rd / "lean.err").write_text(err[:2000])
        for src, dst in (("lean.out", "lean.out.gz"), ("tools.tsv", "tools.tsv.gz")):
            if (w / src).exists():
                with open(w / src, "rb") as fi, gzip.open(rd / dst, "wb") as fo:
                    shutil.copyfileobj(fi, fo)
        lines.append(f"end={int(time.time())}")
        info.write_text("\n".join(lines) + "\n")
        shutil.rmtree(w, ignore_errors=True)
        return i, e

    with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
        for i, e in ex.map(task, range(len(tasks))):
            print(f"difftest task {i} ({' '.join(tasks[i][:2])}): lean exit {e}", flush=True)
    rc, _, _ = sh([sys.executable, AUDIT_DIR / "summarize.py", d / "results", "--tsv", d / "kinds.tsv"],
                  ROOT, d / "summary.txt")
    sys.exit(rc)


def in_k19():
    w = OUT / "extras" / "k19"
    shutil.rmtree(w, ignore_errors=True)
    cnf, _ = gen_graph(w, "cub100", GRAPHS["cub100"])
    lines = []

    def kv(k, v):
        lines.append(f"{k}={v}")
        (w / "result.txt").write_text("\n".join(lines) + "\n")

    e, t, _ = sh(["d4", cnf, "-dDNNF", "-out=in.nnf"], w, w / "d4.log")
    m = re.search(r"^s (\d+)", text(w / "d4.log"), re.M)
    kv("d4_exit", e), kv("d4_s", f"{t:.1f}"), kv("d4_count", m.group(1) if m else "-")
    e, t, _ = sh(["cpog-gen", cnf, "in.nnf", "full.cpog"], w, w / "gen.log")
    kv("gen_exit", e), kv("gen_s", f"{t:.1f}"), kv("full_cpog_bytes", (w / "full.cpog").stat().st_size if (w / "full.cpog").exists() else 0)
    e, t, _ = sh(["cpog-check", cnf, "full.cpog"], w, w / "cc.out")
    out = text(w / "cc.out")
    m = re.search(r"Regular model count = *(\d+)", out)
    kv("cc_exit", e), kv("cc_s", f"{t:.1f}")
    kv("cc_success", "yes" if "FULL-PROOF SUCCESS" in out else "no")
    kv("cc_count", m.group(1) if m else "-")
    for x in ("in.nnf", "full.cpog"):
        (w / x).unlink(missing_ok=True)
    kv("status", "done" if m else "failed")
    sys.exit(0 if m else 1)


def in_k26prep():
    """Certificate of the 4x4 domino tilings and the two Lean files of measurement 1."""
    w = OUT / "extras" / "k26"
    shutil.rmtree(w, ignore_errors=True)
    w.mkdir(parents=True)
    with open(w / "in.cnf", "w") as f:
        subprocess.run([*UVRUN, SCRIPTS / "gen_domino.py", "4"], stdout=f, check=True, env=env_path())
    sh(["d4", "in.cnf", "-dDNNF", "-out=in.nnf"], w, w / "d4.log")
    sh(["cpog-gen-fwd", "-F", "-T", "500", "-G", "in.cnf", "in.nnf", "cert.cpog"], w, w / "gen.log")
    e, _, _ = sh(["cpog2lrat", "in.cnf", "cert.cpog", "ki", "--delete", "--keep", "--inline"], w, w / "c2l.log")
    lrat = text(w / "ki.lrat").splitlines()
    adds = sum(1 for l in lrat if l.split()[1:2] != ["d"])
    hdr = next((l.split() for l in text(w / "ki.cnf").splitlines() if l.startswith("p")), ["", "", "-", "-"])
    stamp = '#eval show IO Unit from do IO.println s!"stamp {← IO.monoMsNow}"'
    for mode in ("kernel", "native"):
        flag = " +kernel" if mode == "kernel" else ""
        (w / f"{mode}.lean").write_text("\n".join([
            "import LRATCatcher.Reflect", "", stamp,
            f'lrat_reflect{flag} dom4_fwd_ki "{w}/ki.cnf" "{w}/ki.lrat"', stamp, "",
            "#print axioms dom4_fwd_ki", ""]))
    (w / "result.txt").write_text(f"c2l_exit={e}\nclauses={hdr[3]}\nadditions={adds}\n")
    sys.exit(e)


def in_paper():
    """Run scripts/paper_numbers.py with its outputs redirected to artifact/out/extras/paper and
    compare them with PAPER/ (lines that are not comments)."""
    p = OUT / "extras" / "paper"
    shutil.rmtree(p, ignore_errors=True)
    (p / "tables").mkdir(parents=True)
    spec = importlib.util.spec_from_file_location("paper_numbers", SCRIPTS / "paper_numbers.py")
    pn = importlib.util.module_from_spec(spec)
    sys.argv = ["paper_numbers.py", "--quiet"]
    spec.loader.exec_module(pn)
    pn.NUMBERS_TEX = p / "numbers.tex"
    pn.TABLES = p / "tables"
    pn.main()
    res = []

    def body(path):
        return [l for l in text(path).splitlines() if l.strip() and not l.lstrip().startswith("%")]

    def macros(path):
        return dict(re.findall(r"^\\newcommand\{\\(\w+)\}\{(.*)\}\s*$", text(path), re.M))

    ref = ROOT / "PAPER"
    a, b = macros(ref / "numbers.tex"), macros(p / "numbers.tex")
    diff = sorted(k for k in a if b.get(k) != a[k])
    hyb = [k for k in diff if k.startswith("ablHyb")]  # from overnight.md, not shipped, not cited
    other = [k for k in diff if k not in hyb]
    res.append(f"numbers.tex={len(a) - len(diff)} of {len(a)} macros identical"
               + (f", {len(hyb)} hybrid-generation macros not cited by the paper differ" if hyb else "")
               + (f", differ: {' '.join(other[:12])}" if other else ""))
    for t in sorted((ref / "tables").glob("*")):
        if t.suffix not in (".tex", ".csv"):
            continue
        new = p / "tables" / t.name
        if not new.exists():
            v = "not written"
        elif body(t) == body(new):
            v = "identical"
        else:
            v = "differs"
        res.append(f"{t.name}={v}")
    code = text(p / "tables" / "app_code.tex")
    m = re.search(r"New code, total & ([\d{},]+)", code)
    m2 = re.search(r"Reused unchanged[^&]*& ([\d{},]+)", code)
    res.append(f"lines new={m.group(1).replace('{,}', '') if m else '-'}")
    res.append(f"lines reused={m2.group(1).replace('{,}', '') if m2 else '-'}")
    (p / "compare.txt").write_text("\n".join(res) + "\n")


INTERNAL = {"streamed": in_streamed, "difftest": in_difftest, "k19": in_k19,
            "k26prep": in_k26prep, "paper": in_paper}


# ---------------------------------------------------------------- main

def do_list():
    print("count-catcher reproduction stages (artifact/reproduce.sh --stage NAME). Wall time and")
    print("peak memory on 4 CPUs with 14 GB (Ubuntu 25.04 image, Intel Xeon E5-2640 v4 of 2016,")
    print("2026-10-08), and the wall time in the TACAS 2026 AE VM (4 vCPUs of an AMD EPYC 9274F")
    print("host, 16 GB, offline, 2026-10-12):\n")
    print(f"  {'stage':<12} {'Xeon':>10}  {'peak':>9}  {'VM':>10}  what it reproduces")
    for name, what, wall, peak, vm in STAGES:
        lines = textwrap.wrap(what, 56)
        print(f"  {name:<12} {wall:>10}  {peak:>9}  {vm:>10}  {lines[0]}")
        for l in lines[1:]:
            print(" " * 50 + l)
    print(f"  {'all':<12} {TOTAL[0]:>10}  {TOTAL[1]:>9}  {TOTAL[4]:>10}  every stage in this order")
    print(f"  {'':<12} {TOTAL[2]:>10}  {TOTAL[3]:>9}  {'':>10}  with --skip-large (showcases 46 min, 9.5 GiB)")
    print("\n  The Xeon totals are of the version of 2026-10-08, without the two order-8 items (about")
    print("  3.5 min there); the VM total is --all of this release. Slow single items on the Xeon")
    print("  (in the VM where measured): r35_13 26 min (18; Table 3's 78.9 s is its Lean time only),")
    print("  q13 20 min, krew6 and td9 13 min each, dom12 9 min (5), tri10 and ded7 7 min each (4).")
    print("  An item prints its line when it ends; while it runs, its output goes to")
    print("  artifact/out/STAGE/ITEM.log.")
    print("\n  Disk: the run needs up to 10 GB beyond the installation (5 GB with --skip-large),")
    print("  for the certificates of the largest showcases; 0.5 GB of logs and results remain.")
    print()
    print(LOG_ONLY)


def main():
    if len(sys.argv) > 2 and sys.argv[1] == "--internal":
        os.chdir(ROOT)
        INTERNAL[sys.argv[2]](*sys.argv[3:])
        return 0
    ap = argparse.ArgumentParser(prog="artifact/reproduce.sh",
                                 description=__doc__.split("\n")[0],
                                 epilog="Stages: " + ", ".join(s[0] for s in STAGES))
    ap.add_argument("--list", action="store_true", help="list the stages and exit")
    ap.add_argument("--all", action="store_true", help="run every stage")
    ap.add_argument("--stage", action="append", nargs="+", default=[], metavar="NAME",
                    help="run these stages (in the order of --list)")
    ap.add_argument("--skip-large", action="store_true",
                    help="skip A358391(6) and A303210(9), the two showcases above 10 GB")
    ap.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1),
                    help="parallelism inside an item (graph drivers, difftest tasks); "
                    "default min(4, CPUs)")
    ap.add_argument("--keep-files", action="store_true",
                    help="keep certificates, node tables and LRAT files (default: files "
                    "above 20 MB are deleted after each item)")
    ap.add_argument("--item", action="append", default=[], metavar="KEY",
                    help="run only these items (tests, showcases, validation, competition, "
                    "streamed), e.g. --stage showcases --item krew6")
    ap.add_argument("--no-check", action="store_true", help="do not run check.py at the end")
    a = ap.parse_args()
    if a.list:
        do_list()
        return 0
    names = [s[0] for s in STAGES]
    want = [x for grp in a.stage for x in grp]
    bad = [x for x in want if x not in names]
    if bad:
        ap.error(f"unknown stage {' '.join(bad)} (stages: {' '.join(names)})")
    if not a.all and not want:
        ap.print_help()
        return 2
    a.stages = names if a.all else [n for n in names if n in want]
    if a.item:  # an item key is the first word of a row of artifact/expected.tsv
        keys = set()
        for line in EXPECTED.read_text().splitlines()[1:]:
            f = line.split("\t")
            if len(f) > 1 and f[0] in a.stages and f[0] in ITEMIZED:
                keys.add(f[1].split(" ")[0])
        unknown = sorted(set(a.item) - keys)
        if unknown:
            ap.error(f"unknown item {' '.join(unknown)} for the stages {' '.join(a.stages)} "
                     f"(items: {' '.join(sorted(keys))})")
    os.environ["CC_REPRO_JOBS"] = str(a.jobs)
    missing = [p for p in (TOOLS / "d4", CC_BIN, LEAN / ".lake/build/lib/lean/CountCatcher.olean")
               if not p.exists()]
    if missing:
        sys.exit("reproduce: not installed (missing " + ", ".join(map(str, missing))
                 + "); run artifact/install.sh, then source artifact/env.sh")
    for t in ("lake", "uv"):
        if not shutil.which(t, path=env_path()["PATH"]):
            sys.exit(f"reproduce: {t} not on PATH; source artifact/env.sh first")
    OUT.mkdir(parents=True, exist_ok=True)
    r = Run(a)
    with open(OUT / "machine.txt", "a") as f:
        mem = next((l.split()[1] for l in text("/proc/meminfo").splitlines() if l.startswith("MemTotal")), "?")
        f.write(f"{time.strftime('%F %T')} host={platform.node()} cpus={os.cpu_count()} "
                f"mem_kb={mem} stages={','.join(a.stages)} jobs={a.jobs} skip_large={a.skip_large}\n")
    t0 = time.time()
    for s in a.stages:
        print(f"[reproduce {time.strftime('%H:%M:%S')}] stage {s}", flush=True)
        ts = time.time()
        STAGE_FN[s](r)
        print(f"[reproduce {time.strftime('%H:%M:%S')}] stage {s} done in {time.time() - ts:.0f} s",
              flush=True)
    print(f"[reproduce] {len(a.stages)} stage(s) in {time.time() - t0:.0f} s; results in "
          f"{RESULTS.relative_to(ROOT)}\n", flush=True)
    if a.no_check:
        return 0
    return subprocess.run([sys.executable, str(ART / "check.py"), "--stage", *a.stages]
                          + (["--item", *a.item] if a.item else [])).returncode


if __name__ == "__main__":
    sys.exit(main())

# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Generates the paper's number macros and table bodies from the evaluation data.

Usage: uv run scripts/paper_numbers.py [--quiet]

Writes PAPER/numbers.tex (one \\newcommand per number), the table bodies
PAPER/tables/{funnel,medians,ablation,showcases}.tex and PAPER/tables/fig3_data.csv, and the
appendix bodies PAPER/tables/app_*.tex (literal numbers, no new macros; see write_appendix).
Rerun it after the final collection replaces the raw files; the input paths are below.

Conventions (also written into the header of numbers.tex):
- Macro names are letters only. Prefix by source: fun (R3 funnel), big (largest proved),
  cmp (R4 comparison with CPOG's checkers), abl (ablations: R4 reverse half, part C, R5,
  hybrid generation, embedded against streamed), sc (R2 showcases), fam (R1 families).
  Digits are spelled out (D4 -> DFour, 14-queens -> QFourteen). Suffixes: Med, Min, Max
  (median and range), N (instances behind a median), Lower (instances where ours is lower).
- Numbers: thousands separator {,} (valid in text and math mode); times in seconds with one
  decimal below 1,000 s and none from 1,000 s on; ratios and factors with two significant
  digits; memory in GB = 2^30 bytes (as rerun.md: kB / 2^20), one decimal from 1 GB on,
  two significant digits below; certificate sizes in decimal GB (10^9 bytes) or MB (10^6).
- A value not yet in the data is \\PH (the paper defines \\PH). Where a partial value exists,
  a companion macro <name>Sofar holds it; it disappears once the value is final, so a paper
  that cites a Sofar macro stops compiling and has to switch to the final one.
"""
from __future__ import annotations

import csv
import io
import math
import re
import statistics
import sys
import tarfile
from decimal import ROUND_HALF_UP, Decimal
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------- inputs (edit here) ---------
EVAL = REPO / "research/eval-2026-10-02"
RAW = EVAL / "rerun_raw"
# Each raw source may be a .tgz or a directory with the same layout (results/...). All
# existing paths of a list are read in order and merged file by file, later ones overriding
# earlier ones: a final R3 tarball overrides the partial one, and an extra R4 tarball (e.g.
# track1_069, the 82nd instance of the rule) extends the 90. Missing paths are skipped.
R3_SOURCES = [RAW / "r3_results_partial.tgz", RAW / "r3_results.tgz", RAW / "r3_results"]
R4_SOURCES = [RAW / "r4_results.tgz", RAW / "r4_results_extra.tgz", RAW / "r4_results"]
R1R2_SOURCES = [RAW / "r1_r2_results.tgz", RAW / "r1_r2_results"]
R5_SOURCES = [RAW / "r5_results.tgz", RAW / "r5_results"]
RERUN_MD = EVAL / "rerun.md"  # cross-check only
# Optional (not in the public tree): section 7, hybrid generation; without it the hybrid
# macros, which the paper does not cite, are \PH.
OVERNIGHT_MD = EVAL / "overnight.md"
PARTC_TSV = REPO / "research/eval-2026-10-01/partc_topdown_table.tsv"
FUNNEL_SBATCH = REPO / "scripts/cluster/rerun_funnel.sbatch"  # stage limits of R3
# Results that do not exist yet; when a file appears, fill in its parser (now all \PH).
LATIN8_DIR = REPO / "research/latin8-2026-10-04"  # order-8 run: assemble.txt, res/*.txt, T.lean
CPOG_1TB_RESULT = None  # the 1 TB run of cpog-lean-check (true memory peak)
# Appendix inputs: acceptance tests (hand suite, Lean-format cases, differential test) and the
# Lean sources whose lines are counted (lrat-catcher: the pinned package that Lake fetched).
# Differential test: records per kind with the rejecting stages, from the rerun on the shipped
# checker and default pipeline (2026-10-07, both routes; research/eval-2026-10-07/difftest_rerun.md,
# written by its contract_audit/summarize.py --tsv). The hand suite's verdicts are those of
# 2026-09-30, which the shipped checker reproduces (difftest_rerun.md).
DIFFTEST_TSV = REPO / "research/eval-2026-10-07/difftest_kinds.tsv"
# constructed certificates: the records of the shipped tools (hand suite plus c26, 2026-10-11)
AUDIT_HAND = REPO / "research/eval-2026-10-07/contract_audit/contract_lean_2026-10-11.txt"
ADV_LEAN = REPO / "lean/test/Adversarial.lean"  # Lean-format cases (reportA blocks)
LEAN_DIR = REPO / "lean"
LRAT_PKG = LEAN_DIR / ".lake/packages/LRATCatcher"

# ---------------------------------------------------------------- outputs --------------------
NUMBERS_TEX = REPO / "PAPER/numbers.tex"
TABLES = REPO / "PAPER/tables"

# ---------------------------------------------------------------- settings -------------------
R4_RULE_GEN_LIMIT_S = 600.0  # R4 set: R3 proved with generation under this
MIN_RATIO_TIME_S = 1.0  # time ratios (generation, solving) only where both times reach this
TABLE_COUNT_MAX_DIGITS = 9  # longer counts appear as a.bc * 10^k in the showcase table
R4_BANDS = [  # full certificate bytes, [lo, hi)
    ("One", "below 10\\,MB", 0, 10e6),
    ("Two", "10 to 100\\,MB", 10e6, 100e6),
    ("Three", "100\\,MB to 1\\,GB", 100e6, 1e9),
    ("Four", "above 1\\,GB", 1e9, math.inf),
]
# R5 instances: tag for macro names, label for the paper
R5_INSTANCES = {
    "q13": ("QThirteen", "13-queens"),
    "q14": ("QFourteen", "14-queens"),
    "ind16": ("GridSixteen", "grid 16"),
    "sp7": ("SpernerSeven", "Sperner 7"),
    "mc2022_track2_011": ("TwoEleven", "track2\\_011"),
    "mc2022_track2_087": ("TwoEightySeven", "track2\\_087"),
    "mc2022_track2_095": ("TwoNinetyFive", "track2\\_095"),
}
R5_VARIANTS = ["r5_text", "r5_trimbin", "r5_keep", "r5_inline"]
# Funnel: e2e.sbatch status -> (stage, outcome). Unknown statuses stop the script.
STAGES = ["d4", "gen", "c2l", "lean"]
STAGE_TAG = {"d4": "DFour", "gen": "Gen", "c2l": "Trans", "lean": "Lean"}
OUTCOMES = ["rejected", "timeout", "oom", "crash"]
OUTCOME_TAG = {"rejected": "Rejected", "timeout": "Timeout", "oom": "Oom", "crash": "Crash"}
# Hand classification of instances that end without a status line (e.g. killed by Slurm's
# wall-time limit, which leaves no status); inspect the Slurm log, then add e.g.
# "mc2022_track1_083": "c2l_timeout".
FUNNEL_STATUS_OVERRIDE: dict[str, str] = {}


def classify_status(status: str) -> tuple[str, str]:
    """Maps an e2e.sbatch status to (stage, outcome); outcome 'passed' only for proved."""
    if status == "proved":
        return "lean", "passed"
    m = re.fullmatch(r"(d4|gen|c2l|lean)_(timeout|killed|fail:(\d+))", status)
    if m:
        stage, kind, code = m.group(1), m.group(2), m.group(3)
        if kind == "timeout":
            return stage, "timeout"
        if kind == "killed":  # exit 137: memory limit (or a signal)
            return stage, "oom"
        if stage == "lean" and code == "1":  # Lean's elaboration error: the check rejected
            return stage, "rejected"
        return stage, "crash"
    if status in ("theorem_file", "no_leandir"):
        return "lean", "crash"
    raise ValueError(f"unknown e2e status {status!r}: extend classify_status")


# ---------------------------------------------------------------- reading --------------------
def read_sources(paths: list[Path]) -> tuple[str, dict[str, str]]:
    """Merged files of all existing paths (later ones override) and a description."""
    used = [p for p in paths if p.exists()]
    if not used:
        raise FileNotFoundError("none of: " + ", ".join(str(p) for p in paths))
    files: dict[str, str] = {}
    for p in used:
        files.update(read_files(p))
    return " + ".join(str(p.relative_to(REPO)) for p in used), files


def read_files(src: Path) -> dict[str, str]:
    """All regular files of a .tgz or a directory, keyed by their path inside it."""
    out: dict[str, str] = {}
    if src.is_dir():
        for p in sorted(src.rglob("*")):
            if p.is_file():
                out[str(p.relative_to(src))] = p.read_text(errors="replace")
    else:
        with tarfile.open(src) as tf:
            for m in tf.getmembers():
                if m.isfile():
                    out[m.name] = tf.extractfile(m).read().decode(errors="replace")
    return out


KV_LINE = re.compile(r"^([A-Za-z][A-Za-z0-9_]*)=(.*)$")


def parse_kv(text: str) -> dict[str, str]:
    """key=value lines, first occurrence wins (the translator's own 'vars=… clauses=…' log
    line repeats the key vars); the translator's 'trim …', 'keep …' and 'inline …' lines
    become keys trim.X, keep.X, inline.X."""
    d: dict[str, str] = {}
    for line in text.splitlines():
        m = KV_LINE.match(line)
        if m and m.group(1) not in d:
            d[m.group(1)] = m.group(2).strip()
        for pre in ("trim", "keep", "inline"):
            if line.startswith(pre + " "):
                for k, v in re.findall(r"(\w+)=(\S+)", line):
                    d.setdefault(f"{pre}.{k}", v)
    return d


def fnum(d: dict, key: str) -> float | None:
    v = d.get(key, "")
    try:
        return float(v)
    except ValueError:
        return None


PART_RE = re.compile(r"part B[^,]*? (\d+) ms, parts A and C (\d+) ms")
ABC_RE = re.compile(r"\(parts A, B, C\) (\d+) ms")


def check_seconds(d: dict) -> tuple[float | None, float | None, float | None, str]:
    """(part B, parts A and C, total check) in seconds and the source used: the keys
    part_b_ms/part_ac_ms, else cmd_info, else lean_out (both cut, at 400 and 800 bytes), else
    the difference of the two count_models stamps (total only)."""
    b, ac = fnum(d, "part_b_ms"), fnum(d, "part_ac_ms")
    if b is not None and ac is not None:
        return b / 1e3, ac / 1e3, (b + ac) / 1e3, "keys"
    for key in ("cmd_info", "lean_out"):
        m = PART_RE.search(d.get(key, ""))
        if m:
            b, ac = float(m.group(1)), float(m.group(2))
            return b / 1e3, ac / 1e3, (b + ac) / 1e3, key
        m = ABC_RE.search(d.get(key, ""))
        if m:
            return None, None, float(m.group(1)) / 1e3, key + " (embedded)"
    st = d.get("stamps", "").split()
    if len(st) == 2:
        return None, None, (int(st[1]) - int(st[0])) / 1e3, "stamps"
    return None, None, None, "none"


# ---------------------------------------------------------------- formatting -----------------
def fmt_int(n: int | float) -> str:
    n = int(round(n))
    s = f"{abs(n):,}".replace(",", "{,}")
    return ("\\ensuremath{-}" if n < 0 else "") + s


def _round(x: float, decimals: int) -> Decimal:
    q = Decimal(1).scaleb(-decimals) if decimals > 0 else Decimal(1)
    return Decimal(repr(x)).quantize(q, rounding=ROUND_HALF_UP)


def fmt_time(s: float) -> str:
    """Seconds: one decimal below 1,000 s, none from 1,000 s on."""
    r = _round(s, 1)
    if r >= 1000:
        return fmt_int(float(_round(s, 0)))
    return f"{r:.1f}"


def fmt_sig2(x: float) -> str:
    """Two significant digits; 100 and more as a rounded integer with separators."""
    if x == 0:
        return "0"
    e = math.floor(math.log10(abs(x)))
    dec = 1 - e
    r = _round(x, dec) if dec > 0 else Decimal(round(x / 10 ** (-dec)) * 10 ** (-dec))
    if r != 0 and math.floor(math.log10(abs(float(r)))) > e:  # 9.96 -> 10
        dec -= 1
        r = _round(x, dec) if dec > 0 else Decimal(round(x / 10 ** (-dec)) * 10 ** (-dec))
    if dec > 0:
        return f"{r:.{dec}f}"
    return fmt_int(float(r))


def fmt_gib_kb(kb: float) -> str:
    return fmt_mem(kb / 2**20)


def fmt_mem(gib: float) -> str:
    """Memory in GB (2^30 bytes): one decimal from 1 GB on, two significant digits below."""
    if gib >= 0.995:
        return f"{_round(gib, 1):.1f}"
    return fmt_sig2(gib)


def fmt_gb(nbytes: float) -> str:
    """Decimal GB with one decimal."""
    return f"{_round(nbytes / 1e9, 1):.1f}"


def fmt_pct(frac: float) -> str:
    return fmt_sig2(100 * frac)


def fmt_count(n: int) -> str:
    return fmt_int(n)


def fmt_sci(n: int, sig: int = 3) -> str:
    s = str(n)
    e = len(s) - 1
    mant = Decimal(s[: sig + 1]).scaleb(-sig) if len(s) > sig else Decimal(s)
    mant = _round(float(mant), sig - 1)
    if mant >= 10:
        mant, e = _round(float(mant) / 10, sig - 1), e + 1
    return f"\\ensuremath{{{mant}\\cdot 10^{{{e}}}}}"


def tex_escape(s: str) -> str:
    return s.replace("_", "\\_")


# ---------------------------------------------------------------- statistics -----------------
def med(xs: list[float]) -> float:
    return statistics.median(xs)


def ratio_list(pairs, min_den: float = 0.0, min_num: float = 0.0):
    """Per-instance ratios num/den, skipping a zero denominator and values below the floors."""
    out = []
    for num, den in pairs:
        if num is None or den is None or den <= 0 or den < min_den or num < min_num:
            continue
        out.append(num / den)
    return out


# ---------------------------------------------------------------- macro emitter --------------
NAME_RE = re.compile(r"^[A-Za-z]+$")


class Emitter:
    def __init__(self) -> None:
        self.lines: list[str] = []
        self.names: set[str] = set()
        self.pending: list[tuple[str, str | None, str]] = []
        self.values: dict[str, str] = {}

    def group(self, title: str, source: str) -> None:
        self.lines += ["", f"% ---- {title}", f"% source: {source}"]

    def note(self, text: str) -> None:
        for line in text.splitlines():
            self.lines.append(f"% {line}")

    def add(self, name: str, value: str | None, *, sofar: str | None = None,
            why: str = "") -> None:
        """value None means not yet in the data: \\PH, plus <name>Sofar if a partial value
        exists."""
        if not NAME_RE.match(name):
            raise ValueError(f"macro name {name!r} is not letters only")
        if name in self.names:
            raise ValueError(f"macro {name} defined twice")
        self.names.add(name)
        if value is None:
            self.lines.append(f"\\newcommand{{\\{name}}}{{\\PH}}" + (f"  % {why}" if why else ""))
            self.pending.append((name, sofar, why))
            self.values[name] = "\\PH"
            if sofar is not None:
                sname = name + "Sofar"
                if sname in self.names:
                    raise ValueError(f"macro {sname} defined twice")
                self.names.add(sname)
                self.lines.append(f"\\newcommand{{\\{sname}}}{{{sofar}}}  % partial, do not cite")
        else:
            self.lines.append(f"\\newcommand{{\\{name}}}{{{value}}}")
            self.values[name] = value

    def add_stats(self, base: str, xs: list[float], fmt, *, pending: bool = False,
                  why: str = "", minmax: bool = True) -> None:
        """base+Med, base+Min, base+Max, base+N."""
        if not xs:
            for suf in (["Med", "Min", "Max"] if minmax else ["Med"]):
                self.add(base + suf, None, why=why or "no data")
            self.add(base + "N", None, why=why or "no data")
            return
        vals = {"Med": fmt(med(xs)), "Min": fmt(min(xs)), "Max": fmt(max(xs))}
        for suf in (["Med", "Min", "Max"] if minmax else ["Med"]):
            if pending:
                self.add(base + suf, None, sofar=vals[suf], why=why)
            else:
                self.add(base + suf, vals[suf])
        if pending:
            self.add(base + "N", None, sofar=str(len(xs)), why=why)
        else:
            self.add(base + "N", str(len(xs)))

    def v(self, name: str) -> str:
        """The macro call for use in a table body."""
        if name not in self.names:
            raise KeyError(name)
        return f"\\{name}"


WARNINGS: list[str] = []


def warn(msg: str) -> None:
    WARNINGS.append(msg)


# ---------------------------------------------------------------- R3 funnel ------------------
def funnel_limits() -> dict[str, str]:
    t = FUNNEL_SBATCH.read_text()
    lim = {}
    for key in ("TO_D4", "TO_GEN", "TO_LEAN"):
        m = re.search(rf"{key}=\$\{{{key}:-(\d+)\}}", t)
        lim[key] = int(m.group(1)) if m else None
    m = re.search(r"#SBATCH --mem=(\d+)G", t)
    lim["MEM_GB"] = int(m.group(1)) if m else None
    return lim


def r3_load() -> tuple[str, dict[str, dict]]:
    src, files = read_sources(R3_SOURCES)
    inst = {}
    for name, text in files.items():
        m = re.search(r"results/funnel/([^/]+)/e2e_stream\.txt$", name)
        if m:
            inst[m.group(1)] = parse_kv(text)
    return src, inst


def r3_state(d: dict, name: str) -> tuple[str, str]:
    """(stage, outcome) of a finished run, or (stage, 'running') with the stage it is in."""
    status = d.get("status") or FUNNEL_STATUS_OVERRIDE.get(name)
    if status:
        return classify_status(status)
    if d.get("d4_exit") is None:
        return "d4", "running"
    if d.get("gen_exit") is None:
        return "gen", "running"
    if d.get("c2l_exit") is None:  # pog_count.py runs between generation and translation
        return "c2l", "running"
    return "lean", "running"


def r3_funnel(em: Emitter, src: str, inst: dict[str, dict]) -> dict:
    lim = funnel_limits()
    em.group("R3 MC2022 funnel: instances per stage and outcome",
             f"{src} (key=value files), limits from "
             f"{FUNNEL_SBATCH.relative_to(REPO)}")
    states = {n: r3_state(d, n) for n, d in inst.items()}
    running = {n: s for n, (s, o) in states.items() if o == "running"}
    total = len(inst)
    si = {s: i for i, s in enumerate(STAGES)}
    em.add("funTotal", str(total))
    # public instances per track, 100 in each of the two tracks (research/eval-2026-09-30/mc2022.md)
    em.add("funPerTrack", "100")
    em.add("funDuplicates", str(2 * 100 - total))
    if running:
        em.add("funRunning", str(len(running)))
        em.note("still running: " + ", ".join(f"{n} ({s})" for n, s in sorted(running.items())))
    else:
        em.add("funRunning", "0")
    em.add("funLimitDFour", fmt_int(lim["TO_D4"]))
    em.add("funLimitGen", fmt_int(lim["TO_GEN"]))
    em.add("funLimitLean", fmt_int(lim["TO_LEAN"]))
    em.add("funLimitMem", str(lim["MEM_GB"]))
    cells = {}
    for k, stage in enumerate(STAGES):
        # entered: reached the stage; final unless a running run is still before it
        entered = sum(1 for n, (s, o) in states.items() if si[s] >= k)
        entered_final = all(si[s] >= k for s in running.values())
        passed = sum(1 for n, (s, o) in states.items()
                     if si[s] > k or (s == stage and o == "passed")
                     or (si[s] > k and o == "running"))
        cell_final = not any(si[s] <= k for s in running.values())
        tag = STAGE_TAG[stage]
        cells[(stage, "entered")] = (f"fun{tag}Entered", entered, entered_final)
        cells[(stage, "passed")] = (f"fun{tag}Passed", passed, cell_final)
        for oc in OUTCOMES:
            if oc == "rejected" and stage != "lean":  # only the Lean check can reject
                continue
            c = sum(1 for n, (s, o) in states.items() if s == stage and o == oc)
            cells[(stage, oc)] = (f"fun{tag}{OUTCOME_TAG[oc]}", c, cell_final)
    for (stage, what), (name, val, final) in cells.items():
        em.add(name, str(val) if final else None, sofar=None if final else str(val),
               why="" if final else "depends on runs still going")
    proved = [n for n, (s, o) in states.items() if o == "passed"]
    final_all = not running
    em.note("number proved with its denominator: \\funProved{} of \\funTotal{}")
    em.add("funProved", str(len(proved)) if final_all else None,
           sofar=None if final_all else str(len(proved)), why="runs still going")
    failed = sum(1 for n, (s, o) in states.items() if o not in ("passed", "running"))
    em.add("funFailed", str(failed) if final_all else None,
           sofar=None if final_all else str(failed), why="runs still going")
    em.note("proved formulas with certificates below 100 MB: the artifact's notebook subset")
    em.add("funProvedSmall", str(sum(1 for n in proved if int(inst[n]["cpog_bytes"]) < 100e6)))
    # consistency of the proved counts
    mism = [n for n in proved if inst[n].get("pog_count_ok") != "yes"]
    used = [n for n in proved if inst[n].get("count_used")]
    em.add("funCountMismatch", str(len(mism)) if final_all else None,
           sofar=None if final_all else str(len(mism)), why="runs still going")
    if mism:
        warn(f"R3: pog_count_ok is not yes on {mism}")
    if used:
        warn(f"R3: count_used (certificate count differs from D4) on {used}")
    return {"states": states, "running": running, "proved": proved, "lim": lim}


def r3_medians(em: Emitter, inst: dict[str, dict], st: dict) -> None:
    proved = st["proved"]
    pend = bool(st["running"])
    why = "median over the proved; runs still going"
    em.group("R3 MC2022 funnel: medians over the proved instances (b5 nodes)",
             "R3 key=value files: d4_s, gen_s, c2l_s, lean_s, part times, *_maxrss_kb")
    col = lambda k: [fnum(inst[n], k) for n in proved if fnum(inst[n], k) is not None]
    parts = {n: check_seconds(inst[n]) for n in proved}
    for n, (b, ac, tot, how) in parts.items():
        if how not in ("keys", "cmd_info"):
            em.note(f"{n}: part times from {how}")
    em.add_stats("funDFour", col("d4_s"), fmt_time, pending=pend, why=why)
    em.add_stats("funGen", col("gen_s"), fmt_time, pending=pend, why=why)
    em.add_stats("funTrans", col("c2l_s"), fmt_time, pending=pend, why=why)
    em.add_stats("funLean", col("lean_s"), fmt_time, pending=pend, why=why)
    em.add_stats("funPartB", [p[0] for p in parts.values() if p[0] is not None], fmt_time,
                 pending=pend, why=why)
    em.add_stats("funPartAC", [p[1] for p in parts.values() if p[1] is not None], fmt_time,
                 pending=pend, why=why)
    em.add_stats("funCheck", [p[2] for p in parts.values() if p[2] is not None], fmt_time,
                 pending=pend, why=why)
    em.add_stats("funGenMem", [x / 2**20 for x in col("gen_maxrss_kb")], fmt_mem,
                 pending=pend, why=why)
    em.add_stats("funLeanMem", [x / 2**20 for x in col("lean_maxrss_kb")], fmt_mem,
                 pending=pend, why=why)

    em.group("Largest proved MC2022 instance (R3): certificate and count",
             "R3 key=value files: cpog_bytes (forward-only certificate), count")
    if proved:
        big = max(proved, key=lambda n: int(inst[n]["cpog_bytes"]))
        cnt = lambda n: inst[n].get("count_used") or inst[n]["count"]
        dig = max(proved, key=lambda n: len(cnt(n)))
        vals = {
            "bigCertGB": fmt_gb(int(inst[big]["cpog_bytes"])),
            "bigCertInstance": tex_escape(big.removeprefix("mc2022_")),
            "bigCertLean": fmt_time(fnum(inst[big], "lean_s")),
            "bigCertLeanMem": fmt_gib_kb(fnum(inst[big], "lean_maxrss_kb")),
            "bigCountDigits": fmt_int(len(cnt(dig))),
            "bigCountInstance": tex_escape(dig.removeprefix("mc2022_")),
        }
        for k, v in vals.items():
            em.add(k, None if pend else v, sofar=v if pend else None,
                   why="a run still going may be larger")
        # the Lean timeouts: the largest one by certificate, named in the Q1 prose
        tos = [n for n, (s, o) in st["states"].items() if s == "lean" and o == "timeout"]
        if tos:
            t = max(tos, key=lambda n: int(inst[n].get("cpog_bytes") or 0))
            em.add("funLeanTimeoutInstance", tex_escape(t.removeprefix("mc2022_")))
            cb = inst[t].get("cpog_bytes")
            em.add("funLeanTimeoutCertGB", fmt_gb(int(cb)) if cb else None,
                   why="no certificate size recorded for the timed-out run")
        # generated but not yet proved: say so, these are the candidates
        for n, s in st["running"].items():
            cb = inst[n].get("cpog_bytes")
            if cb and int(cb) > int(inst[big]["cpog_bytes"]):
                em.note(f"running {n} has a larger certificate: {fmt_gb(int(cb))} GB ({s})")
            c = inst[n].get("count")
            if c and len(c) > len(cnt(dig)):
                em.note(f"running {n} has a longer count: {len(c)} digits ({s})")


# ---------------------------------------------------------------- R4 comparison --------------
def r4_load() -> tuple[str, dict[str, dict]]:
    src, files = read_sources(R4_SOURCES)
    inst: dict[str, dict] = {}
    for name, text in files.items():
        m = re.search(r"results/cpog/([^/]+)/(e2e_stream|cpog_baseline)\.txt$", name)
        if m:
            inst.setdefault(m.group(1), {})[m.group(2)] = parse_kv(text)
    return src, inst


def r4_rows(inst: dict[str, dict]) -> list[dict]:
    rows = []
    for n, f in sorted(inst.items()):
        e, c = f.get("e2e_stream", {}), f.get("cpog_baseline", {})
        b, ac, chk, how = check_seconds(e)
        limits = []
        if e.get("status") != "proved":
            limits.append("ours:" + e.get("status", "missing"))
        for pre, nm in (("gen_full", "gen_full"), ("vc", "cpog-lean-check"), ("cc", "cpog-check")):
            ex = c.get(f"{pre}_exit")
            if ex != "0":
                limits.append(f"{nm}:" + {"124": "timeout", "137": "killed"}.get(ex or "", f"exit {ex}"))
        rows.append({
            "instance": n,
            "family": not n.startswith("mc2022_"),
            "full_bytes": fnum(c, "gen_full_bytes"),
            "fwd_bytes": fnum(e, "cpog_bytes"),
            "d4_s": fnum(e, "d4_s"),
            "gen_s": fnum(e, "gen_s"),
            "gen_full_s": fnum(c, "gen_full_s"),
            "c2l_s": fnum(e, "c2l_s"),
            "part_b_s": b, "part_ac_s": ac, "check_s": chk, "check_src": how,
            "lean_s": fnum(e, "lean_s"),
            "lean_gib": (fnum(e, "lean_maxrss_kb") or 0) / 2**20 or None,
            "vc_s": fnum(c, "vc_s"), "vc_gib": (fnum(c, "vc_maxrss_kb") or 0) / 2**20 or None,
            "cc_s": fnum(c, "cc_s"), "cc_gib": (fnum(c, "cc_maxrss_kb") or 0) / 2**20 or None,
            "vc_ok": c.get("vc_success") == "yes" and c.get("vc_count_ok") == "yes",
            "cc_success": c.get("cc_success") == "yes",
            "cc_ok": c.get("cc_success") == "yes" and c.get("cc_count_ok") == "yes",
            "ours_ok": e.get("status") == "proved",
            "vc_done": c.get("vc_exit") == "0", "cc_done": c.get("cc_exit") == "0",
            "gen_full_done": c.get("gen_full_exit") == "0",
            "limit": ";".join(limits) if limits else "none",
            "host": e.get("host", ""),
        })
    return rows


def r4_macros(em: Emitter, src: str, rows: list[dict], r3: dict | None,
              r3inst: dict | None) -> dict:
    em.group("R4 comparison with CPOG's checkers", f"{src} "
             "(results/cpog/<instance>/{e2e_stream,cpog_baseline}.txt)")
    em.note("ratios are ours over cpog-lean-check, medians of the per-instance ratios, over the "
            "jointly completed runs (runs that hit a limit are excluded)")
    n = len(rows)
    mc = [r for r in rows if not r["family"]]
    fam = [r for r in rows if r["family"]]
    em.add("cmpN", str(n))
    em.add("cmpNMcTwentyTwentyTwo", str(len(mc)))
    em.add("cmpNFamilies", str(len(fam)))
    em.note("check time (part B + parts A, C) from the keys part_b_ms/part_ac_ms, else from "
            "cmd_info, else from lean_out, else the count_models stamp difference")
    for r in rows:
        if r["check_src"] not in ("keys", "cmd_info"):
            em.note(f"{r['instance']}: check time from {r['check_src']}")
    # rule check against R3
    if r3 is not None:
        rule = sorted(nm for nm in r3["proved"]
                      if (fnum(r3inst[nm], "gen_s") or 1e9) < R4_RULE_GEN_LIMIT_S)
        have = {r["instance"] for r in mc}
        missing = [x for x in rule if x not in have]
        extra = sorted(have - set(rule))
        em.add("cmpRuleN", str(len(rule)) if not r3["running"] else None,
               sofar=None if not r3["running"] else str(len(rule)),
               why="R3 still running")
        em.add("cmpRuleGenLimit", fmt_int(R4_RULE_GEN_LIMIT_S))
        if missing:
            em.note("rule set (R3 proved, generation under the limit) lacks R4 data for: "
                    + ", ".join(missing))
            warn(f"R4: instances of the rule without R4 data: {missing}")
        if extra:
            em.note("R4 instances outside the rule: " + ", ".join(extra))
            warn(f"R4: instances outside the rule: {extra}")
    ok = [r for r in rows if r["ours_ok"]]
    joint_vc = [r for r in ok if r["vc_done"] and r["vc_ok"]]
    joint_cc = [r for r in ok if r["cc_done"]]
    joint_pipe = [r for r in joint_vc if r["gen_full_done"]]
    em.add("cmpOursProved", str(len(ok)))
    em.add("cmpVcCorrect", str(sum(r["vc_ok"] for r in rows)))
    em.add("cmpCcSuccess", str(sum(r["cc_success"] for r in rows)))
    em.add("cmpCcCorrect", str(sum(r["cc_ok"] for r in rows)))
    wrong = [r["instance"] for r in rows if r["cc_success"] and not r["cc_ok"]]
    em.add("cmpCcWrong", str(len(wrong)))
    em.note("cpog-check reported success with a wrong count on: " + ", ".join(wrong))
    em.add("cmpLimitHits", str(sum(r["limit"] != "none" for r in rows)))
    # medians of the absolute values
    em.note("medians of absolute values (s, GB)")
    em.add_stats("cmpOurCheck", [r["check_s"] for r in ok], fmt_time)
    share = [r["part_b_s"] / r["check_s"] for r in ok
             if r["part_b_s"] is not None and r["check_s"]]
    em.note("share of the forward check (part B) in the check time, per run; validity and "
            "reverse are timed together, so no three-way split")
    em.add("cmpFwdSharePct", fmt_int(100 * statistics.median(share)))
    em.add("cmpFwdShareN", str(len(share)))
    em.add_stats("cmpOurLean", [r["lean_s"] for r in ok], fmt_time)
    em.add_stats("cmpOurTrans", [r["c2l_s"] for r in ok], fmt_time)
    em.add_stats("cmpVc", [r["vc_s"] for r in joint_vc], fmt_time)
    em.add_stats("cmpCc", [r["cc_s"] for r in joint_cc], fmt_time)
    em.add_stats("cmpOurMem", [r["lean_gib"] for r in ok], fmt_mem)
    em.add_stats("cmpVcMem", [r["vc_gib"] for r in joint_vc], fmt_mem)
    em.add_stats("cmpCcMem", [r["cc_gib"] for r in joint_cc], fmt_mem)
    em.add_stats("cmpGenFwd", [r["gen_s"] for r in ok], fmt_time)
    em.add_stats("cmpGenFull", [r["gen_full_s"] for r in rows if r["gen_full_done"]], fmt_time)
    em.add_stats("cmpFullMB", [r["full_bytes"] / 1e6 for r in rows], fmt_sig2)

    def boundary(base, num, den, rs):
        xs = ratio_list([(num(r), den(r)) for r in rs])
        em.add_stats(base, xs, fmt_sig2)
        em.add(base + "Lower", str(sum(1 for x in xs if x < 1)))
        return xs

    em.note("boundaries: checking prepared input (part B + parts A, C against the checker), "
            "translation plus theorem (translator + Lean total against the checker), pipeline "
            "after d4 (forward generation + translator + Lean against full generation + checker)")
    boundary("cmpBoundCheck", lambda r: r["check_s"], lambda r: r["vc_s"], joint_vc)
    boundary("cmpBoundThm", lambda r: r["c2l_s"] + r["lean_s"], lambda r: r["vc_s"], joint_vc)
    boundary("cmpBoundPipe", lambda r: r["gen_s"] + r["c2l_s"] + r["lean_s"],
             lambda r: r["gen_full_s"] + r["vc_s"], joint_pipe)
    boundary("cmpBoundMem", lambda r: r["lean_gib"], lambda r: r["vc_gib"], joint_vc)
    # medians of the summed absolute times for the median table
    em.add("cmpThmOursMed", fmt_time(med([r["c2l_s"] + r["lean_s"] for r in joint_vc])))
    em.add("cmpPipeOursMed", fmt_time(med([r["gen_s"] + r["c2l_s"] + r["lean_s"] for r in joint_pipe])))
    em.add("cmpPipeVcMed", fmt_time(med([r["gen_full_s"] + r["vc_s"] for r in joint_pipe])))
    em.add("cmpPipeCcMed", fmt_time(med([r["gen_full_s"] + r["cc_s"] for r in joint_cc if r["gen_full_done"]])))
    em.add("cmpPipeN", str(len(joint_pipe)))
    # check time against solving time (D4)
    em.note(f"check time over solving time (d4), per instance, only instances with d4 at least "
            f"{MIN_RATIO_TIME_S} s")
    solv = [r for r in joint_vc if (r["d4_s"] or 0) >= MIN_RATIO_TIME_S]
    em.add_stats("cmpSolveOurCheck", [r["check_s"] / r["d4_s"] for r in solv], fmt_sig2)
    em.add_stats("cmpSolveOurLean", [r["lean_s"] / r["d4_s"] for r in solv], fmt_sig2)
    em.add_stats("cmpSolveVc", [r["vc_s"] / r["d4_s"] for r in solv], fmt_sig2)
    em.add_stats("cmpSolveCc", [r["cc_s"] / r["d4_s"] for r in solv if r["cc_done"]], fmt_sig2)
    # size bands
    em.group("R4 size bands (full certificate bytes)", "R4 key=value files: gen_full_bytes")
    band_check = []
    for tag, label, lo, hi in R4_BANDS:
        rs = [r for r in joint_vc if lo <= r["full_bytes"] < hi]
        em.add(f"cmpBand{tag}Label", label)
        em.add(f"cmpBand{tag}N", str(len(rs)))
        if not rs:
            continue
        lean = ratio_list([(r["lean_s"], r["vc_s"]) for r in rs])
        mem = ratio_list([(r["lean_gib"], r["vc_gib"]) for r in rs])
        chk = ratio_list([(r["check_s"], r["vc_s"]) for r in rs])
        em.add(f"cmpBand{tag}LeanRatio", fmt_sig2(med(lean)))
        em.add(f"cmpBand{tag}MemRatio", fmt_sig2(med(mem)))
        em.add(f"cmpBand{tag}CheckRatio", fmt_sig2(med(chk)))
        band_check.append(med(chk))
    em.add("cmpBandCheckRatioMin", fmt_sig2(min(band_check)))
    em.add("cmpBandCheckRatioMax", fmt_sig2(max(band_check)))
    # largest certificate of R4
    big = max(rows, key=lambda r: r["full_bytes"])
    em.group("R4 largest full certificate", "R4 key=value files")
    em.add("cmpBigInstance", tex_escape(big["instance"].removeprefix("mc2022_")))
    em.add("cmpBigFullGB", fmt_gb(big["full_bytes"]))
    em.add("cmpBigOurCheck", fmt_time(big["check_s"]))
    em.add("cmpBigOurLean", fmt_time(big["lean_s"]))
    em.add("cmpBigOurMem", fmt_mem(big["lean_gib"]))
    em.add("cmpBigVc", fmt_time(big["vc_s"]))
    em.add("cmpBigVcMem", fmt_mem(big["vc_gib"]))
    em.add("cmpBigCc", fmt_time(big["cc_s"]))
    em.add("cmpBigCcMem", fmt_mem(big["cc_gib"]))
    em.group("Memory peak of CPOG's verified checker without the common limit (1 TB run)",
             "not run yet")
    em.add("cmpVcTruePeak", None, why="1 TB run not done")
    em.add("cmpVcTruePeakInstance", None, why="1 TB run not done")
    return {"rows": rows, "joint_vc": joint_vc, "joint_cc": joint_cc, "joint_pipe": joint_pipe,
            "solv": solv}


def write_fig3_csv(rows: list[dict]) -> None:
    TABLES.mkdir(parents=True, exist_ok=True)
    cols = ["instance", "family", "full_cert_bytes", "fwd_cert_bytes", "our_check_s",
            "our_lean_total_s", "our_lean_mem_gib", "vc_s", "vc_mem_gib", "cc_s", "cc_mem_gib",
            "cc_count_ok", "vc_count_ok", "limit"]
    buf = io.StringIO()
    w = csv.writer(buf, lineterminator="\n")
    w.writerow(cols)
    r3 = lambda x: "" if x is None else f"{x:.3f}"
    for r in sorted(rows, key=lambda r: r["full_bytes"]):
        w.writerow([r["instance"], int(r["family"]), int(r["full_bytes"]), int(r["fwd_bytes"]),
                    r3(r["check_s"]), r3(r["lean_s"]), r3(r["lean_gib"]), r3(r["vc_s"]),
                    r3(r["vc_gib"]), r3(r["cc_s"]), r3(r["cc_gib"]), int(r["cc_ok"]),
                    int(r["vc_ok"]), r["limit"]])
    (TABLES / "fig3_data.csv").write_text(buf.getvalue())


# ---------------------------------------------------------------- ablations ------------------
def abl_reverse_half(em: Emitter, rows: list[dict]) -> None:
    em.group("Ablation: reverse half left out (SCPOG's choice, measured on CPOG certificates)",
             "R4 key=value files: gen_full_bytes over cpog_bytes (forward-only), gen_full_s "
             "over gen_s")
    em.note("the forward generator is cpog-gen-fwd -F -T 500 -G, the full one the unpatched "
            "cpog-gen, so the time factor includes the -T/-G patch (measured separately "
            "on 2026-10-02: time 0.87 to 1.10 times, sizes equal except two instances)")
    em.note("factors are without over with the choice (> 1: the choice saves)")
    ok = [r for r in rows if r["gen_full_done"] and r["ours_ok"]]
    em.add_stats("ablRevBytes", ratio_list([(r["full_bytes"], r["fwd_bytes"]) for r in ok]),
                 fmt_sig2)
    em.note(f"generation time: only instances where both generations take at least "
            f"{MIN_RATIO_TIME_S} s")
    em.add_stats("ablRevGen", ratio_list([(r["gen_full_s"], r["gen_s"]) for r in ok],
                                         min_den=MIN_RATIO_TIME_S, min_num=MIN_RATIO_TIME_S),
                 fmt_sig2)


def abl_partc(em: Emitter) -> None:
    em.group("Ablation: part C by 63-clause batches (M4) against top-down short-circuit "
             "(best of M2, M3; unverified Lean implementation) and per-clause bottom-up (M1)",
             f"{PARTC_TSV.relative_to(REPO)} (columns m4_s, m3_s, m2_s, m1_s)")
    rows = list(csv.DictReader(PARTC_TSV.open(), delimiter="\t"))
    num = lambda v: None if v in ("", "timeout") else float(v)
    td, pc, cens = [], [], []
    for r in rows:
        m4, m3, m2, m1 = (num(r[k]) for k in ("m4_s", "m3_s", "m2_s", "m1_s"))
        if m4 and m3 and m2:
            td.append(min(m2, m3) / m4)
        if m4 and m1:
            pc.append(m1 / m4)
        elif m4 and r["m1_s"] == "timeout":
            cens.append(r["inst"])
        if "REJECT" in r["verdicts"]:
            warn(f"part C: a method rejected on {r['inst']}")
    em.add("ablPartcN", str(len(rows)))
    em.add_stats("ablPartcTd", td, fmt_sig2)
    em.add("ablPartcTdLower", str(sum(1 for x in td if x > 1)))
    em.note("per-clause: M1 timeouts (1,800 s) are bounds and excluded: " + ", ".join(cens))
    em.add_stats("ablPartcPc", pc, fmt_sig2)
    em.add("ablPartcPcCensored", str(len(cens)))


def r5_load() -> tuple[str, dict[tuple[str, str], dict]]:
    src, files = read_sources(R5_SOURCES)
    out = {}
    for name, text in files.items():
        m = re.fullmatch(r"(?:.*/)?([^/]+)\.(r5_\w+)\.1\.txt", name)
        if m and "/aux/" not in "/" + name:
            out[(m.group(1), m.group(2))] = parse_kv(text)
    return src, out


def abl_r5(em: Emitter) -> None:
    src, data = r5_load()
    em.group("Ablation of part B (R5): 7 instances by 4 variants, one repetition, slurm-cpu01",
             f"{src} (<inst>.<variant>.1.txt: partB_s, lean_s, lean_rss_mb, "
             "c2l_s, translator log)")
    em.note("variants: text = --delete, text; trimbin = --trim --binary; keep = --keep --binary; "
            "inline = --keep --inline --binary. Steps: text to trimbin (trimming and binary "
            "together, no trimmed-text variant), trimbin to keep (mask), keep to inline. "
            "Factors are before over after (> 1: the step saves); memory in GB")
    for (inst, var), d in data.items():
        if d.get("status") != "proved" or d.get("wrong") not in ("0", None):
            warn(f"R5: {inst} {var} status {d.get('status')}")
    steps = {  # name -> (before, after, key)
        "TrimBinPartB": ("r5_text", "r5_trimbin", "partB_s"),
        "TrimBinLean": ("r5_text", "r5_trimbin", "lean_s"),
        "KeepPartB": ("r5_trimbin", "r5_keep", "partB_s"),
        "KeepLean": ("r5_trimbin", "r5_keep", "lean_s"),
        "KeepMem": ("r5_trimbin", "r5_keep", "lean_rss_mb"),
        "InlinePartB": ("r5_keep", "r5_inline", "partB_s"),
        "InlineLean": ("r5_keep", "r5_inline", "lean_s"),
        "InlineTrans": ("r5_keep", "r5_inline", "c2l_s"),
        "InlineTransMem": ("r5_keep", "r5_inline", "c2l_rss_mb"),
        "AllPartB": ("r5_text", "r5_inline", "partB_s"),
        "AllLean": ("r5_text", "r5_inline", "lean_s"),
    }
    insts = [i for i in R5_INSTANCES if all((i, v) in data for v in R5_VARIANTS)]
    missing = [i for i in R5_INSTANCES if i not in insts]
    if missing:
        warn(f"R5: incomplete instances {missing}")
    em.add("ablRFiveN", str(len(insts)))
    per: dict[str, list[float]] = {k: [] for k in steps}
    for inst in insts:
        tag = R5_INSTANCES[inst][0]
        for k, (a, b, key) in steps.items():
            f = fnum(data[(inst, a)], key) / fnum(data[(inst, b)], key)
            per[k].append(f)
            em.add(f"abl{k}{tag}", fmt_sig2(f))
        before = fnum(data[(inst, "r5_trimbin")], "lean_rss_mb") / 1024
        after = fnum(data[(inst, "r5_keep")], "lean_rss_mb") / 1024
        em.add(f"ablKeepMemBefore{tag}", fmt_mem(before))
        em.add(f"ablKeepMemAfter{tag}", fmt_mem(after))
        k = data[(inst, "r5_keep")]
        share = int(k["c2l_keep_ones"]) / int(k["c2l_keep_len"])
        per.setdefault("KeepShare", []).append(share)
        em.add(f"ablKeepShare{tag}", fmt_pct(share))
        em.add(f"ablInlineTransMemPlus{tag}",
               fmt_int(fnum(data[(inst, "r5_inline")], "c2l_rss_mb")
                       - fnum(data[(inst, "r5_keep")], "c2l_rss_mb")))
    em.note("medians and ranges over the R5 instances")
    for k in steps:
        em.add_stats(f"abl{k}", per[k], fmt_sig2)
    em.add_stats("ablKeepShare", per["KeepShare"], fmt_pct)
    em.add("ablTrimBinSlower", str(sum(1 for x in per["TrimBinPartB"] if x < 1)))
    slower = [R5_INSTANCES[i][1] for i, x in zip(insts, per["TrimBinPartB"]) if x < 1]
    em.note("trimmed binary slower than text in part B on: " + ", ".join(slower))


HYB_ROW = re.compile(r"^\|\s*(\d+)-queens, `-M (\d+)`\s*\|(.*)\|\s*$")


def abl_hybrid(em: Emitter) -> None:
    if not OVERNIGHT_MD.exists():
        em.group("Ablation: hybrid generation on 13- and 14-queens, structural over hybrid",
                 f"{OVERNIGHT_MD.relative_to(REPO)} (not shipped; the paper does not cite these "
                 "macros)")
        warn(f"hybrid: {OVERNIGHT_MD.relative_to(REPO)} missing, the hybrid macros are \\PH")
        for b in ("ablHybGen", "ablHybCert", "ablHybMem", "ablHybLean"):
            em.add_stats(b, [], fmt_sig2, why="hybrid data not shipped")
        return
    em.group("Ablation: hybrid generation on 13- and 14-queens, structural over hybrid",
             f"{OVERNIGHT_MD.relative_to(REPO)} section 7, Markdown table (no raw key=value "
             "data locally; collect_0955.out has only the check side)")
    text = OVERNIGHT_MD.read_text()
    sec = text.split("## 7.", 1)[1] if "## 7." in text else ""
    rows = []
    for line in sec.splitlines():
        m = HYB_ROW.match(line)
        if m:
            cells = [c.strip() for c in m.group(3).split("|")]
            pair = lambda c: [float(x.replace(",", "")) for x in
                              re.findall(r"[\d,]+\.?\d*", c.split("(")[0] if "(" not in c
                                         else c)][:2]
            gen, rss, cert = pair(cells[0]), pair(cells[1]), pair(cells[2])
            lean = re.findall(r"([\d,]+\.?\d*) \(([\d.]+)\)", cells[4])
            rows.append({"n": int(m.group(1)), "M": int(m.group(2)), "gen": gen, "rss": rss,
                         "cert": cert, "lean": [float(a.replace(",", "")) for a, _ in lean]})
    if not rows:
        warn("hybrid: no rows parsed from overnight.md section 7")
        for b in ("ablHybGen", "ablHybCert", "ablHybMem"):
            em.add_stats(b, [], fmt_sig2, why="no data")
        return
    words = {13: "QThirteen", 14: "QFourteen"}
    for r in rows:
        t = words.get(r["n"], f"Q{r['n']}")
        em.add(f"ablHybGen{t}", fmt_sig2(r["gen"][0] / r["gen"][1]))
        em.add(f"ablHybGenBefore{t}", fmt_time(r["gen"][0]))
        em.add(f"ablHybGenAfter{t}", fmt_time(r["gen"][1]))
        em.add(f"ablHybCert{t}", fmt_sig2(r["cert"][0] / r["cert"][1]))
        em.add(f"ablHybMem{t}", fmt_sig2(r["rss"][0] / r["rss"][1]))
        em.add(f"ablHybLean{t}", fmt_sig2(r["lean"][0] / r["lean"][1]))
        em.add(f"ablHybM{t}", fmt_int(r["M"]))
    em.add_stats("ablHybGen", [r["gen"][0] / r["gen"][1] for r in rows], fmt_sig2)
    em.add_stats("ablHybCert", [r["cert"][0] / r["cert"][1] for r in rows], fmt_sig2)
    em.add_stats("ablHybMem", [r["rss"][0] / r["rss"][1] for r in rows], fmt_sig2)
    em.add_stats("ablHybLean", [r["lean"][0] / r["lean"][1] for r in rows], fmt_sig2)


EMBED_TSV = REPO / "research/eval-2026-10-04/embedded_streamed.tsv"


KERNEL_TSV = REPO / "research/eval-2026-10-04/kernel_only.tsv"


UNSH_TSV = REPO / "research/eval-2026-10-05/unshortened.tsv"


def unshortened(em: Emitter) -> None:
    """The check on the refutation as the generator wrote it (translator --delete --binary only,
    no trimming, keep mask or inlining) against cpog-lean-check in the same job, on the 91
    comparison instances (2026-10-05, b4 nodes, research/eval-2026-10-05/unshortened.md)."""
    em.group("Unshortened refutation against cpog-lean-check (within-job ratios, 91 instances)",
             f"{UNSH_TSV.relative_to(REPO) if UNSH_TSV.exists() else 'missing'}")
    if not UNSH_TSV.exists():
        for n in ("unshN", "unshCheckMed", "unshCheckMax", "unshCheckLower", "unshLratFactorMed",
                  "unshCheckFactorMed", "unshThmMed", "unshPipeMed"):
            em.add(n, None, why="unshortened run missing")
        return
    lines = UNSH_TSV.read_text().splitlines()
    rows = [dict(zip(lines[0].split("\t"), l.split("\t"))) for l in lines[1:]]
    rows = [r for r in rows if r["status_B"] == "proved" and r["vc_count_ok"] == "yes"]
    f = lambda r, k: float(r[k])
    chk = [f(r, "check_s_B") / f(r, "vc_s") for r in rows]
    em.add("unshN", fmt_int(len(rows)))
    em.add("unshCheckMed", fmt_sig2(med(chk)))
    em.add("unshCheckMax", fmt_sig2(max(chk)))
    em.add("unshCheckLower", fmt_int(sum(1 for x in chk if x < 1)))
    em.add("unshLratFactorMed", fmt_sig2(med([f(r, "lrat_mb_B") / f(r, "lrat_mb_A") for r in rows
                                              if f(r, "lrat_mb_A") > 0])))
    em.add("unshCheckFactorMed", fmt_sig2(med([f(r, "check_s_B") / f(r, "check_s_A") for r in rows
                                               if f(r, "check_s_A") > 0])))
    em.add("unshThmMed", fmt_sig2(med([(f(r, "c2l_s_B") + f(r, "lean_s_B")) / f(r, "vc_s")
                                       for r in rows])))
    em.add("unshPipeMed", fmt_sig2(med([(f(r, "gen_s") + f(r, "c2l_s_B") + f(r, "lean_s_B"))
                                        / (f(r, "gen_full_s") + f(r, "vc_s")) for r in rows
                                        if f(r, "gen_full_s") + f(r, "vc_s") > 0])))


def kernel_only(em: Emitter) -> None:
    """lrat-catcher's kernel mode against native evaluation on the forward refutations of
    small domino boards (2026-10-04, slurm-cpu01, masked and inlined proofs, 64 GB)."""
    rows = [dict(zip(KERNEL_TSV.read_text().splitlines()[0].split("\t"), l.split("\t")))
            for l in KERNEL_TSV.read_text().splitlines()[1:]] if KERNEL_TSV.exists() else []
    em.group("Kernel-only check of small forward refutations (masked and inlined, 64 GB)",
             f"{KERNEL_TSV.relative_to(REPO) if KERNEL_TSV.exists() else 'missing'} "
             "(from research/eval-2026-10-04/embedded_streamed.md, measurement 1)")
    by = {r["board"]: r for r in rows}
    for tag, board in (("Four", "4x4"), ("FourSix", "4x6"), ("Six", "6x6")):
        r = by.get(board)
        em.add(f"ker{tag}Clauses", fmt_int(int(r["clauses"])) if r else None, why="no kernel run")
        em.add(f"ker{tag}Adds", fmt_int(int(r["additions"])) if r else None, why="no kernel run")
        em.add(f"ker{tag}NativeMs", fmt_int(int(r["native_ms"])) if r else None, why="no kernel run")
        if r and r["kernel_cmd_s"]:
            em.add(f"ker{tag}KernelS", fmt_int(round(float(r["kernel_cmd_s"]))))
            em.add(f"ker{tag}KernelGB", fmt_sig2(float(r["kernel_gb"])))
    em.add("kerLimitGB", fmt_int(int(rows[0]["limit_gb"])) if rows else None, why="no kernel run")


def abl_embed(em: Emitter) -> None:
    """Embedded against streamed (2026-10-04, slurm-cpu01, three repetitions): the check time
    that count_models reports, embedded over streamed, on the same text LRAT (S1) and against
    the streamed default with keep mask, inlining and binary format (S2)."""
    rows = [dict(zip(EMBED_TSV.read_text().splitlines()[0].split("\t"), l.split("\t")))
            for l in EMBED_TSV.read_text().splitlines()[1:]] if EMBED_TSV.exists() else []
    em.group("Ablation: embedded against streamed (check time, embedded over streamed)",
             f"{EMBED_TSV.relative_to(REPO) if EMBED_TSV.exists() else 'missing'} "
             "(E_check_ms, S1_check_ms same text LRAT, S2_check_ms streamed default)")
    em.note("process time (4 to 13 s) is start-up noise at these sizes; three repetitions, "
            "ratios of the medians per instance as the TSV gives them")
    same = [float(r["E/S1_check"]) for r in rows]
    default = [float(r["E/S2_check"]) for r in rows]
    em.add_stats("ablEmbedSame", same, fmt_sig2, why="no embedded-against-streamed measurement")
    em.add_stats("ablEmbedDef", default, fmt_sig2, why="no embedded-against-streamed measurement")
    time_same = [float(r["E/S1_time"]) for r in rows]
    em.add_stats("ablEmbedTime", time_same, fmt_sig2, why="no embedded-against-streamed measurement")


# ---------------------------------------------------------------- showcases (R2) -------------
SHOWCASES = [  # key, macro tag, use, label, level
    ("tri10", "TriTen", "Composition of certified counts", "Triangle-free graphs on 10 vertices, A006785",
     "composition"),
    ("lat7", "LatinSeven", "", "Latin squares of order 7", "composition"),
    ("ded7", "DedekindSeven", "One count as an end-to-end theorem", "Dedekind's number $M(7)$",
     "object theorem"),
    ("krew6", "KrewerasSix", "", "A358391(6), Kreweras", "object theorem"),
    ("sp7", "SpernerSeven", "", "A396728(7), Sperner", "object theorem"),
    ("td9", "TotDomNine", "", "A303210(9), total domination", "object theorem"),
    ("td10", "TotDomTen", "", "A303210(10), total domination", "object theorem"),
    ("r35_13", "RamseyThirteen", "A count as a hypothesis",
     "The $(3,5)$-Ramsey graph on 13 vertices is unique", "composition"),
]
NEW_OEIS_VALUES = {"krew6", "sp7", "td9", "td10"}  # not listed in the OEIS at time of writing; dagger in Table 6
APP_LABEL = {  # shorter row labels for the appendix table (no wrapped rows)
    "tri10": "Triangle-free graphs",
    "r35_13": "$(3,5)$-Ramsey graph",
    "lat7": "Latin squares, order 7", "lat8": "Latin squares, order 8", "ded7": "Dedekind's $M(7)$",
    "krew6": "A358391(6)", "sp7": "A396728(7)", "td9": "A303210(9)", "td10": "A303210(10)",
}


def showcases(em: Emitter) -> list[dict]:
    src, files = read_sources(R1R2_SOURCES)
    get = lambda key, f: files.get(f"results/showcases/{key}/{f}", "")
    em.group("R2 showcases (slurm-cpu01)", f"{src} (results/showcases/<key>/: "
             "result.txt, summary.tsv, assemble.txt, res/*.txt, T.lean)")
    em.note("Lean is the whole Lean run (lean_s); Latin 7: the four leaves plus the assembly")
    out = []
    for key, tag, use, label, level in SHOWCASES:
        res = parse_kv(get(key, "result.txt"))
        row = {"key": key, "tag": tag, "use": use, "label": label, "level": level}
        if key in ("tri10", "r35_13"):
            summ = list(csv.DictReader(io.StringIO(get(key, "summary.tsv")), delimiter="\t"))
            kinds = [s["kind"] for s in summ]
            row["count"] = int(res["orbits"])
            row["terms"] = len(summ)
            row["lean"] = float(res["lean_s"])
            em.add(f"sc{tag}Labelled", fmt_count(int(res["labelled"])))
            em.add(f"sc{tag}Terms", str(len(summ)))
            em.add(f"sc{tag}Certified", str(kinds.count("cpog")))
            em.add(f"sc{tag}Refuted", str(kinds.count("unsat")))
            em.add(f"sc{tag}CertGB", fmt_gb(sum(int(s["cpog_bytes"]) for s in summ)))
            ok = res.get("status") == "proved"
        elif key == "lat7":
            asm = parse_kv(get(key, "assemble.txt"))
            leaves = [parse_kv(t) for n, t in files.items()
                      if re.search(rf"results/showcases/{key}/res/[^/]+\.txt$", n)]
            m = re.search(r"IsLatin L\} = (\d+)", get(key, "T.lean"))
            row["count"] = int(m.group(1)) if m else None
            row["terms"] = sum(1 for k in asm if k.startswith("class_"))
            row["lean"] = sum(float(lf["lean_s"]) for lf in leaves) + float(asm["asm_s"])
            em.add(f"sc{tag}Reduced", fmt_count(int(asm["count"])))
            em.add(f"sc{tag}Fibres", str(row["terms"]))
            em.add(f"sc{tag}Leaves", str(len(leaves)))
            em.add(f"sc{tag}AssemblyLean", fmt_time(float(asm["asm_s"])))
            ok = asm.get("status") == "proved" and all(lf.get("status") == "proved"
                                                       for lf in leaves)
            if row["count"] is None:
                warn("showcase lat7: no IsLatin count in T.lean")
        else:
            row["count"] = int(res["count"])
            row["terms"] = 1
            row["lean"] = float(res["lean_s"])
            em.add(f"sc{tag}CertGB", fmt_gb(int(res["cpog_bytes"])))
            ok = res.get("status") == "proved"
        if not ok:
            warn(f"showcase {key}: not proved")
        em.add(f"sc{tag}Count", fmt_count(row["count"]))
        em.add(f"sc{tag}CountDigits", str(len(str(row["count"]))))
        if len(str(row["count"])) > TABLE_COUNT_MAX_DIGITS:
            em.add(f"sc{tag}CountSci", fmt_sci(row["count"]))
        em.add(f"sc{tag}Composed", str(row["terms"]))
        em.add(f"sc{tag}Lean", fmt_time(row["lean"]))
        out.append(row)
    em.add("scN", str(len(out)))
    em.group("Latin squares of order 8 (b501, arrays 121333 and 121334, assembly 121335)",
             f"{LATIN8_DIR.relative_to(REPO)} (assemble.txt, res/<leaf>.txt, T.lean)")
    em.note("Lean is the sum of the leaf Lean times plus the assembly; certificate sizes are "
            "the sums over the leaves (CPOG before translation, LRAT binary and inlined)")
    asm = parse_kv((LATIN8_DIR / "assemble.txt").read_text())
    leaves = [parse_kv(f.read_text()) for f in sorted((LATIN8_DIR / "res").glob("*.txt"))]
    m = re.search(r"IsLatin L\} = (\d+)", (LATIN8_DIR / "T.lean").read_text())
    ok = asm.get("status") == "proved" and all(lf.get("status") == "proved" for lf in leaves)
    if not ok:
        warn("Latin 8: not proved")
    cnt = int(m.group(1))
    em.add("scLatinEightReduced", fmt_count(int(asm["count"])))
    em.add("scLatinEightCount", fmt_count(cnt))
    em.add("scLatinEightCountDigits", str(len(str(cnt))))
    em.add("scLatinEightCountSci", fmt_sci(cnt))
    em.add("scLatinEightFibres", str(sum(1 for k in asm if k.startswith("class_"))))
    em.add("scLatinEightLeaves", str(len(leaves)))
    em.add("scLatinEightComposed", str(len(leaves)))
    lean_total = sum(float(lf["lean_s"]) for lf in leaves) + float(asm["asm_s"])
    em.add("scLatinEightLean", fmt_time(lean_total))
    em.add("scLatinEightLeanHours", fmt_sig2(lean_total / 3600))
    em.add("scLatinEightAssemblyLean", fmt_time(float(asm["asm_s"])))
    em.add("scLatinEightNativeAxioms", fmt_int(int(asm["axioms_native"])))
    cpog = [int(lf["cpog_bytes"]) for lf in leaves]
    em.add("scLatinEightCertTB", fmt_sig2(sum(cpog) / 1e12))
    em.add("scLatinEightLratTB", fmt_sig2(sum(int(lf["lrat_bytes"]) for lf in leaves) / 1e12))
    em.add("scLatinEightCertMaxGB", fmt_gb(max(cpog)))
    em.add("scLatinEightCertMedGB", fmt_gb(sorted(cpog)[len(cpog) // 2]))
    em.add("scLatinEightGenHours", fmt_sig2(sum(float(lf["gen_s"]) for lf in leaves) / 3600))
    em.add("scLatinEightDFourHours", fmt_sig2(sum(float(lf["d4_s"]) for lf in leaves) / 3600))
    em.add("scLatinEightTransHours", fmt_sig2(sum(float(lf["c2l_s"]) for lf in leaves) / 3600))
    em.add("scLatinEightLeanMaxGB", fmt_sig2(max(float(lf["lean_rss_mb"]) for lf in leaves) / 1024))
    em.add("scLatinEightLeanMaxS", fmt_time(max(float(lf["lean_s"]) for lf in leaves)))
    em.add("scLatinEightGenMaxS", fmt_time(max(float(lf["gen_s"]) for lf in leaves)))
    row8 = {"key": "lat8", "tag": "LatinEight", "use": "", "label": "Latin squares of order 8",
            "level": "composition", "count": cnt, "terms": len(leaves), "lean": lean_total}
    out.insert(next(i for i, r in enumerate(out) if r["key"] == "lat7") + 1, row8)
    return out


def families(em: Emitter) -> None:
    src, files = read_sources(R1R2_SOURCES)
    fam = {m.group(1): parse_kv(t) for n, t in files.items()
           if (m := re.search(r"results/families/([^/]+)/e2e_stream\.txt$", n))}
    em.group("R1 families (validation, slurm-cpu01)",
             f"{src} (results/families/<inst>/e2e_stream.txt)")
    em.add("famN", str(len(fam)))
    em.add("famProved", str(sum(d.get("status") == "proved" for d in fam.values())))
    if "q14" in fam:
        d = fam["q14"]
        em.add("famQFourteenLean", fmt_time(fnum(d, "lean_s")))
        em.add("famQFourteenGen", fmt_time(fnum(d, "gen_s")))
        em.add("famQFourteenCertGB", fmt_gb(fnum(d, "cpog_bytes")))
        em.add("famQFourteenLeanMem", fmt_gib_kb(fnum(d, "lean_maxrss_kb")))
    em.add("famLeanMax", fmt_time(max(fnum(d, "lean_s") for d in fam.values())))
    big = max(fam.values(), key=lambda d: fnum(d, "cpog_bytes"))
    em.add("famCertMaxGB", fmt_gb(fnum(big, "cpog_bytes")))


# ---------------------------------------------------------------- table bodies ---------------
DASH = "--"


def write_tables(em: Emitter, sc_rows: list[dict]) -> None:
    TABLES.mkdir(parents=True, exist_ok=True)
    v = em.v
    gen = "% Generated by scripts/paper_numbers.py (body only; needs PAPER/numbers.tex).\n"
    # Table 3: funnel. Columns: stage (limit) & reached & rejected & timeout & out of memory
    # & crash & passed (Lean: proved)
    lab = {"d4": f"d4 ({v('funLimitDFour')}~s)",
           "gen": f"Generation ({v('funLimitGen')}~s)",
           "c2l": f"Translation ({v('funLimitGen')}~s)",
           "lean": f"Lean, theorem stage ({v('funLimitLean')}~s)"}
    lines = [gen + "% columns: stage (time limit) & reached & rejected & timeout & out of "
             "memory & crash & passed (Lean: proved)"]
    for s in STAGES:
        t = STAGE_TAG[s]
        rej = v(f"fun{t}Rejected") if s == "lean" else DASH
        lines.append(" & ".join([lab[s], v(f"fun{t}Entered"), rej, v(f"fun{t}Timeout"),
                                 v(f"fun{t}Oom"), v(f"fun{t}Crash"), v(f"fun{t}Passed")])
                     + " \\\\")
    (TABLES / "funnel.tex").write_text("\n".join(lines) + "\n")
    # Table 4: medians. Columns: comparison & count-catcher & cpog-lean-check & cpog-check
    # & median ratio (ours over cpog-lean-check) & ours lower & n
    lines = [gen + "% columns: comparison & count-catcher & cpog-lean-check & cpog-check & "
             "median of per-instance ratios (count-catcher over cpog-lean-check) & instances "
             "where count-catcher is lower & jointly completed runs"]
    rows = [
        ("Checks after translation (s)", "cmpOurCheckMed", "cmpVcMed", "cmpCcMed",
         "cmpBoundCheck"),
        ("Translation and Lean run (s)", "cmpThmOursMed", "cmpVcMed", "cmpCcMed",
         "cmpBoundThm"),
        ("Pipeline after d4 (s)", "cmpPipeOursMed", "cmpPipeVcMed", "cmpPipeCcMed",
         "cmpBoundPipe"),
        ("Peak memory (GB)", "cmpOurMemMed", "cmpVcMemMed", "cmpCcMemMed", "cmpBoundMem"),
    ]
    for label, a, b, c, base in rows:
        lines.append(" & ".join([label, v(a), v(b), v(c), v(base + "Med"), v(base + "Lower"),
                                 v(base + "N")]) + " \\\\")
    # the unshortened-refutation run (research/eval-2026-10-05/unshortened.tsv) has ratios
    # only, no absolute medians
    lines.append(" & ".join(["Checks, unshortened refutation", DASH, DASH, DASH,
                             v("unshCheckMed"), v("unshCheckLower"), v("unshN")]) + " \\\\")
    lines.append(" & ".join(["Correct count reported", v("cmpOursProved"), v("cmpVcCorrect"),
                             v("cmpCcCorrect"), DASH, DASH, v("cmpN")]) + " \\\\")
    (TABLES / "medians.tex").write_text("\n".join(lines) + "\n")
    # Table: medians per certificate size (the R4 size bands). Columns: full certificate size
    # & n & median per-instance ratio of count-catcher over cpog-lean-check for the whole Lean
    # process, the check alone and peak memory
    lines = [gen + "% columns: full certificate size & jointly completed runs & median of the "
             "per-instance ratios (count-catcher over cpog-lean-check) for the whole Lean "
             "process & for the check alone & for peak memory"]
    for b in ("One", "Two", "Three", "Four"):
        lines.append(" & ".join([v(f"cmpBand{b}Label"), v(f"cmpBand{b}N"),
                                 v(f"cmpBand{b}LeanRatio"), v(f"cmpBand{b}CheckRatio"),
                                 v(f"cmpBand{b}MemRatio")]) + " \\\\")
    (TABLES / "bands.tex").write_text("\n".join(lines) + "\n")
    # Table 5: ablation. Columns: design choice & metric & n & median factor & range
    lines = [gen + "% columns: design choice & metric & instances & median factor & range; "
             "factor = without over with the choice (> 1: the choice saves); the clause share "
             "is a percentage"]

    def rng(b):
        return f"{v(b + 'Min')}--{v(b + 'Max')}"

    def row(choice, metric, b, pct=False):
        m = v(b + "Med") + ("\\%" if pct else "")
        r = rng(b) + ("\\%" if pct else "")
        lines.append(" & ".join([choice, metric, v(b + "N"), m, r]) + " \\\\")

    row("Deletions left out", "certificate bytes", "ablRevBytes")
    row("", "generation time", "ablRevGen")
    row("Bit-parallel reverse check", "vs.\\ top-down evaluation", "ablPartcTd")
    row("", "vs.\\ sweep per clause", "ablPartcPc")
    row("Trimmed binary refutation", "forward check time", "ablTrimBinPartB")
    row("Keep mask", "Lean time", "ablKeepLean")
    row("", "Lean memory", "ablKeepMem")
    row("", "clauses of $\\Phi$ loaded", "ablKeepShare", pct=True)
    row("Inlining", "forward check time", "ablInlinePartB")
    row("", "translator time", "ablInlineTrans")
    row("All three shortening steps", "forward check time", "ablAllPartB")
    # Hybrid generation (ablHybGen, ablHybCert) is not in the table (since 2026-10-05): its
    # baseline lacked -T 500 -G, only the queens rows favour it, and the idea is Bryant et
    # al.'s hybrid generator; the macros stay in numbers.tex.
    (TABLES / "ablation.tex").write_text("\n".join(lines) + "\n")
    # the streamed-against-embedded rows are an appendix table since 2026-10-07 (page budget)
    lines = [gen + "% appendix body: streamed against embedded, same columns as the ablation table"]
    row("Streamed refutation", "check time, same proof", "ablEmbedSame")
    row("", "check time, with mask", "ablEmbedDef")
    (TABLES / "app_stream.tex").write_text("\n".join(lines) + "\n")
    # Table 6: showcases. Columns: use & showcase & level & counts composed & count & Lean s
    lines = [gen + "% columns: theorem & certified counts composed & count & Lean time (s); "
             "a row per use group spans the table"]
    first = True
    for r in sc_rows:
        if r["use"]:
            if not first:
                lines.append("\\addlinespace")
            lines.append("\\multicolumn{4}{@{}l}{\\emph{" + r["use"] + "}} \\\\")
        first = False
        t = r["tag"]
        cnt = v(f"sc{t}CountSci") if f"sc{t}CountSci" in em.names else v(f"sc{t}Count")
        label = r["label"] + ("$^\\dagger$" if r["key"] in NEW_OEIS_VALUES else "")
        lines.append(" & ".join(["\\quad " + label, v(f"sc{t}Composed"), cnt,
                                 v(f"sc{t}Lean")]) + " \\\\")
    (TABLES / "showcases.tex").write_text("\n".join(lines) + "\n")


# ---------------------------------------------------------------- appendix bodies ------------
# The appendix tables carry literal numbers (no macros are added, so numbers.tex is unchanged
# by them), formatted by the conventions above; values that the main text already has as a
# macro (the showcases' Lean times, the native axioms of Latin order 8) are cited by macro.
APP_GEN = "% Generated by scripts/paper_numbers.py (appendix body only).\n"


def fmt_size(nbytes: float, unit: float) -> str:
    """Bytes in MB (unit 1e6) or GB (1e9): no decimal from 1,000 on, one from 1 on, two
    significant digits below 1."""
    x = nbytes / unit
    if _round(x, 1) >= 1000:
        return fmt_int(x)
    if x >= 0.995:
        return f"{_round(x, 1):.1f}"
    return fmt_sig2(x)


def fmt_table_count(n: int) -> str:
    return fmt_sci(n) if len(str(n)) > TABLE_COUNT_MAX_DIGITS else fmt_count(n)


AXIOM_BLOCK = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")


def native_axioms(lean_out: str) -> int:
    """Largest number of native-evaluation axioms over the theorems that #print axioms lists
    (the headline theorem of a file depends on all of them)."""
    counts = [sum("_native" in a for a in m.group(2).split(","))
              for m in AXIOM_BLOCK.finditer(lean_out)]
    if not counts:
        raise ValueError("no #print axioms output")
    return max(counts)


def app_showcases(em: Emitter, sc_rows: list[dict]) -> None:
    """Resources per showcase theorem, rows and group rows as in the showcase table."""
    _, files = read_sources(R1R2_SOURCES)
    get = lambda key, f: files.get(f"results/showcases/{key}/{f}", "")
    v = em.v
    lines = [APP_GEN + "% columns: theorem & summands (certified counts) & size (GB) & d4 (s, summed) & "
             "generation (s, summed) & Lean (s, macro of the showcase table) & peak Lean memory "
             "(GB, largest run) & native-evaluation axioms; a row per use group spans the table"]
    first = True
    for r in sc_rows:
        key = r["key"]
        if key == "lat8":
            leaves = [parse_kv(f.read_text()) for f in sorted((LATIN8_DIR / "res").glob("*.txt"))]
            asm = parse_kv((LATIN8_DIR / "assemble.txt").read_text())
        elif key == "lat7":
            leaves = [parse_kv(t) for n, t in sorted(files.items())
                      if re.search(rf"results/showcases/{key}/res/[^/]+\.txt$", n)]
            asm = parse_kv(get(key, "assemble.txt"))
        if key in ("lat7", "lat8"):
            certs = len(leaves)
            size = sum(int(lf["cpog_bytes"]) for lf in leaves)
            gen = sum(float(lf["gen_s"]) for lf in leaves)
            d4 = sum(float(lf["d4_s"]) for lf in leaves)
            mem_mb = max([float(lf["lean_rss_mb"]) for lf in leaves] + [float(asm["asm_rss_mb"])])
            native = int(asm["axioms_native"])
            if key == "lat7" and native != native_axioms(get(key, "lean.out")):
                warn("showcase lat7: axioms_native differs from #print axioms")
        elif key in ("tri10", "r35_13"):
            summ = list(csv.DictReader(io.StringIO(get(key, "summary.tsv")), delimiter="\t"))
            res = parse_kv(get(key, "result.txt"))
            certs = len(summ)
            size = sum(int(s["cpog_bytes"]) if s["kind"] == "cpog" else int(s["lrat_bytes"])
                       for s in summ)
            gen = sum(float(s["gen_s"]) for s in summ)
            d4 = sum(float(s["d4_s"]) for s in summ)
            mem_mb = float(res["lean_peak_mb"])
            native = native_axioms(get(key, "lean.out"))
        else:
            res = parse_kv(get(key, "result.txt"))
            certs, size, gen = 1, int(res["cpog_bytes"]), float(res["gen_s"])
            d4 = float(res["d4_s"])
            mem_mb = float(res["lean_peak_mb"])
            native = native_axioms(get(key, "lean.out"))
        if certs != int(em.values[f"sc{r['tag']}Composed"]):
            warn(f"showcase {key}: {certs} certificates against Composed")
        if r["use"]:
            if not first:
                lines.append("\\addlinespace")
            lines.append("\\multicolumn{8}{@{}l}{\\emph{" + r["use"] + "}} \\\\")
        first = False
        nat = v("scLatinEightNativeAxioms") if key == "lat8" else fmt_int(native)
        lines.append(" & ".join(["\\hangindent=1em\\hangafter=0 " + APP_LABEL.get(key, r["label"]), fmt_int(certs),
                                 fmt_size(size, 1e9), fmt_time(d4),
                                 fmt_time(gen), v(f"sc{r['tag']}Lean"),
                                 fmt_mem(mem_mb / 1024), nat]) + " \\\\")
    (TABLES / "app_showcases.tex").write_text("\n".join(lines) + "\n")


FAMILY_GROUPS = ["Domino tilings", "Queens", "Independent sets of grids",
                 "Independent sets of graphs"]
FAMILY_GRAPH_NAMES = {"cub": "random cubic", "games120": "games120",
                      "homer": "homer"}


def family_label(key: str, d: dict) -> tuple[int, tuple, str]:
    """(group index, sort key, label) of an R1 instance, from its family field and size."""
    fam = d.get("family", "").split()
    kind, n = fam[0], int(fam[1]) if len(fam) > 1 and fam[1].isdigit() else None
    if kind == "domino":
        return 0, (n,), f"${n}\\times {n}$ board"
    if kind == "queens":
        return 1, (n,), f"$n={n}$"
    if kind == "grid":
        return 2, (n,), f"${n}\\times {n}$ grid"
    vertices = int(d["vars"])
    if kind == "hypercube":
        return 3, (vertices, key), f"hypercube $Q_{{{n}}}$, {fmt_int(vertices)} vertices"
    if kind == "edges":
        name = next(lab for pre, lab in FAMILY_GRAPH_NAMES.items() if key.startswith(pre))
        return 3, (vertices, key), f"{name}, {fmt_int(vertices)} vertices"
    raise ValueError(f"R1 instance {key}: unknown family {d.get('family')!r}")


def app_families() -> None:
    _, files = read_sources(R1R2_SOURCES)
    fam = {m.group(1): parse_kv(t) for n, t in files.items()
           if (m := re.search(r"results/families/([^/]+)/e2e_stream\.txt$", n))}
    rows = sorted((family_label(k, d), k) for k, d in fam.items())
    lines = [APP_GEN + "% columns: instance & count & certificate (MB) & generation (s) & "
             "Lean (s) & peak Lean memory (GB); a row per family spans the table"]
    group = None
    for (g, _, label), k in rows:
        d = fam[k]
        if d.get("status") != "proved" or d.get("pog_count_ok") != "yes":
            warn(f"R1 {k}: status {d.get('status')}, pog_count_ok {d.get('pog_count_ok')}")
        if g != group:
            if group is not None:
                lines.append("\\addlinespace")
            lines.append("\\multicolumn{6}{@{}l}{\\emph{" + FAMILY_GROUPS[g] + "}} \\\\")
            group = g
        lines.append(" & ".join(["\\quad " + label, fmt_table_count(int(d["count"])),
                                 fmt_size(fnum(d, "cpog_bytes"), 1e6), fmt_time(fnum(d, "gen_s")),
                                 fmt_time(fnum(d, "lean_s")),
                                 fmt_gib_kb(fnum(d, "lean_maxrss_kb"))]) + " \\\\")
    (TABLES / "app_families.tex").write_text("\n".join(lines) + "\n")


STAGE_LABEL = {"d4": "d4", "gen": "Generation", "c2l": "Translation", "lean": "Lean"}
OUTCOME_LABEL = {"rejected": "rejected", "timeout": "timeout", "oom": "out of memory",
                 "crash": "crash"}


def app_competition(inst: dict[str, dict], st: dict) -> None:
    """The proved competition formulas by certificate size (longtable body), and the failed
    ones by stage and outcome."""
    if st["running"]:
        warn("appendix: R3 runs still going, competition tables are partial")
    proved = sorted(st["proved"], key=lambda n: (int(inst[n]["cpog_bytes"]), n))
    lines = [APP_GEN + "% two halves side by side; columns (twice): formula & certificate (MB) & "
             "generation (s) & Lean (s) & peak Lean memory (GB); sorted by certificate size, "
             "the first half in the left columns"]
    cells = []
    for n in proved:
        d = inst[n]
        cells.append(" & ".join([tex_escape(n.removeprefix("mc2022_")),
                                 fmt_size(int(d["cpog_bytes"]), 1e6), fmt_time(fnum(d, "gen_s")),
                                 fmt_time(fnum(d, "lean_s")),
                                 fmt_gib_kb(fnum(d, "lean_maxrss_kb"))]))
    half = (len(cells) + 1) // 2
    for i in range(half):
        right = cells[half + i] if half + i < len(cells) else " & & & & "
        lines.append(cells[i] + " & " + right + " \\\\")
    (TABLES / "app_competition.tex").write_text("\n".join(lines) + "\n")
    lines = [APP_GEN + "% columns: stage & outcome & formulas & their names; the counts are "
             "those of the funnel table"]
    for stage in STAGES:
        for oc in OUTCOMES:
            names = sorted(n.removeprefix("mc2022_") for n, (s, o) in st["states"].items()
                           if s == stage and o == oc)
            if names:
                lines.append(" & ".join([STAGE_LABEL[stage], OUTCOME_LABEL[oc], str(len(names)),
                                         ", ".join(tex_escape(x) for x in names)]) + " \\\\")
    (TABLES / "app_failed.tex").write_text("\n".join(lines) + "\n")


def app_miscount(em: Emitter, rows: list[dict], r4inst: dict[str, dict]) -> None:
    """The R4 instance with the smallest correct count on which cpog-check reported success
    with a wrong count: the count of the theorem and the count cpog-check printed, as the
    macros miscountFormula, miscountOurs and miscountPrinted (the table body is kept)."""
    wrong = []
    for r in rows:
        if not (r["cc_success"] and not r["cc_ok"]):
            continue
        e = r4inst[r["instance"]].get("e2e_stream", {})
        c = r4inst[r["instance"]].get("cpog_baseline", {})
        ours = int(e.get("count_used") or e["count"])
        if c.get("vc_count") != str(ours) or c.get("count") != str(ours):
            warn(f"R4 {r['instance']}: theorem count, D4 count and cpog-lean-check disagree")
        wrong.append((ours, r["instance"], int(c["cc_count"])))
    ours, name, printed = min(wrong)
    if name.startswith("mc2022_"):
        label = "competition formula " + tex_escape(name.removeprefix("mc2022_"))
    else:  # a validation family: its group and label as in the family table
        g, _, lab = family_label(name, r4inst[name]["e2e_stream"])
        label = lab  # the row label of the family table
    em.group("R4 smallest miscount of cpog-check (appendix)", "results/compare/<instance>/")
    em.add("miscountFormula", label)
    em.add("miscountOurs", fmt_count(ours))
    em.add("miscountPrinted", fmt_count(printed))
    lines = [APP_GEN + "% rows: formula; count of the theorem (equal to d4's and to "
             "cpog-lean-check's); count printed by cpog-check"]
    lines.append(f"Formula & {label} \\\\")
    lines.append(f"Count of the theorem & {fmt_count(ours)} \\\\")
    lines.append(f"Count printed by cpog-check & {fmt_count(printed)} \\\\")
    (TABLES / "app_miscount.tex").write_text("\n".join(lines) + "\n")


# Conditions in the order in which checkAll tests them (the reverse check before the forward
# check): (check, condition, stage names). Stage names are the audit driver's
# (contract_lean.txt, with node and clause indices removed; contract_audit.md section 3.3) and
# the kind of report of a Lean-format case in Adversarial.lean.
ADV_CONDITIONS = [
    ("universe", "every variable of $F$ lies in the universe", ["cnf-wf"]),
    ("", "the node table is over the $V$ variables of the theorem", ["pog-V"]),
    ("validity", "every argument is an earlier variable", ["A-arg"]),
    ("", "the arguments of a product have disjoint supports", ["A-prod-overlap"]),
    ("", "every exclusion hint cites a defining clause of an earlier node", ["A-sum-hint-ref"]),
    ("", "the exclusion of a sum follows by unit propagation from its hints", ["A-sum-rup"]),
    ("", "the root is declared", ["A-root-range"]),
    ("reverse", "neither an argument nor the root is a negated node", ["C-negation"]),
    ("", "the root implies every clause of $F$ that is not a tautology", ["C-clause"]),
    ("forward", "the refutation is well-formed LRAT", ["B-parse"]),
    ("", "every addition follows from its hints by unit propagation, and the last "
         "is the empty clause", ["B"]),
]
ADV_REPORT_STAGE = [("does not follow by strict RUP", "A-sum-rup"),
                    ("does not cite a defining clause", "A-sum-hint-ref"),
                    ("is not an earlier variable", "A-arg")]


def app_adversarial() -> None:
    """Certificates rejected per acceptance condition (first failing condition): the hand
    suite through the audit driver plus the Lean-format cases of Adversarial.lean, and the
    certificates of the differential test (both routes, research/eval-2026-10-07)."""
    hand: dict[str, int] = {}
    hand_acc = 0
    for line in AUDIT_HAND.read_text().splitlines():
        m = re.match(r"^R (\S+) (ACCEPT|REJECT) stage=(\S+) count=(\S+) exp=(\S+) bf=(\S+)", line)
        if not m:
            continue
        if m.group(2) == "ACCEPT":
            hand_acc += 1
            if m.group(4) != m.group(6):
                warn(f"hand suite: {m.group(1)} accepted with count {m.group(4)}, "
                     f"enumeration {m.group(6)}")
            continue
        stage = re.sub(r"-node\d+", "", m.group(3))
        stage = re.sub(r"^(C-clause|pog-V)\d+$", r"\1", stage)
        stage = {"B-check": "B"}.get(stage, stage)
        hand[stage] = hand.get(stage, 0) + 1
    reports = re.findall(r'info: some\s+"([^"]*)"\s*-/\s*#guard_msgs in\s*#eval reportA',
                         ADV_LEAN.read_text())
    for msg in reports:
        stage = next((s for key, s in ADV_REPORT_STAGE if key in msg), None)
        if stage is None:
            raise ValueError(f"Adversarial.lean: unclassified report {msg!r}")
        hand[stage] = hand.get(stage, 0) + 1
    # differential test: every record of both routes, unmutated or with one mutation
    gen: dict[str, int] = {}
    total = accepted = 0
    with DIFFTEST_TSV.open() as f:
        for row in csv.DictReader(f, delimiter="\t"):
            records, acc = int(row["records"]), int(row["accepted"])
            rej = 0
            for item in filter(None, row["rejected"].split(",")):
                stage, k = item.rsplit(":", 1)
                gen[stage] = gen.get(stage, 0) + int(k)
                rej += int(k)
            if rej + acc != records:
                warn(f"difftest: {row['kind']} stages do not add up")
            total += records
            accepted += acc
    known = {s for _, _, ss in ADV_CONDITIONS for s in ss}
    for s in set(hand) | set(gen):
        if s not in known:
            raise ValueError(f"acceptance tests: stage {s!r} has no condition row")
    lines = [APP_GEN + "% columns: check & condition & constructed certificates rejected at it "
             "& generated certificates rejected at it (differential test); last rows: accepted "
             "(each with the count of enumeration) and total"]
    for i, (check, cond, stages) in enumerate(ADV_CONDITIONS):
        if check and i:
            lines.append("\\addlinespace")
        h = sum(hand.get(s, 0) for s in stages)
        g = sum(gen.get(s, 0) for s in stages)
        if h == 0:
            warn(f"acceptance tests: no constructed certificate for {cond!r}")
        lines.append(" & ".join([check, cond, fmt_int(h), fmt_int(g)]) + " \\\\")
    hand_total = hand_acc + sum(hand.values())
    if sum(gen.values()) + accepted != total:
        warn("audit: rejections and acceptances do not add up to the records")
    lines.append("\\midrule")
    lines.append(" & ".join(["\\multicolumn{2}{@{}l}{accepted, each with the count that "
                             "enumeration gives}", fmt_int(hand_acc), fmt_int(accepted)]) + " \\\\")
    lines.append(" & ".join(["\\multicolumn{2}{@{}l}{total}", fmt_int(hand_total),
                             fmt_int(total)]) + " \\\\")
    (TABLES / "app_adversarial.tex").write_text("\n".join(lines) + "\n")


# Lean sources by role: (label, files relative to lean/). "Pog.lean#parse" is the section of
# Pog.lean from the heading "## Parsing" to the heading "## Checking and counting",
# "Pog.lean#check" the rest of the file. Every .lean file of CountCatcherChecker/ and CountCatcherMath/ is in
# exactly one role or in CODE_EXCLUDED.
CODE_ROLES = [
    ("Executable checker, \\texttt{lean/CountCatcherChecker}, without Mathlib", [
        ("Specification: models, POGs, the contract", ["CountCatcherChecker/Spec.lean"]),
        ("Parser of the node table", ["CountCatcherChecker/Pog.lean#parse"]),
        ("Validity check", ["CountCatcherChecker/Pog.lean#check", "CountCatcherChecker/Popcount.lean"]),
        ("Forward check: the clauses of $\\Phi$, keep mask", ["CountCatcherChecker/Fwd.lean",
                                                              "CountCatcherChecker/FwdSel.lean"]),
        ("Reverse check", ["CountCatcherChecker/Rev.lean", "CountCatcherChecker/RevFast.lean"]),
        ("Composition of the three checks", ["CountCatcherChecker/Check.lean"]),
        ("Compiled encoders", ["CountCatcherChecker/EdgeCnf.lean", "CountCatcherChecker/CliqueCnf.lean"]),
    ]),
    ("Proofs and front end, \\texttt{lean/CountCatcherMath}, with Mathlib", [
        ("Soundness of the checks and of their composition",
         [f"CountCatcherMath/{m}.lean" for m in ("Semantics", "Count", "Indep", "PogSound",
                                           "Popcount", "Fwd", "FwdSel", "Rev", "RevFast",
                                           "Main", "Check")]),
        ("Composition of counts: family lemmas, symmetry, splits",
         [f"CountCatcherMath/{m}.lean" for m in ("Family", "Symmetry", "CycleType", "Split")]),
        ("Encoders and encoding lemmas of the families", ["CountCatcherMath/Families/*.lean"]),
        ("The \\texttt{count\\_models} and \\texttt{\\#export\\_cnf} commands and their error messages", ["CountCatcherMath/Command.lean", "CountCatcherMath/Diag.lean",
                                           "CountCatcher.lean"]),
    ]),
]
CODE_EXCLUDED = {"CountCatcherChecker/RevTD.lean": "unverified top-down baseline",
                 "CountCatcherMath/Families/DedekindCorner.lean": "M(8) by corner classes, a run after the submission (rehearsal 2026-10-07)",
                 "CountCatcherChecker/Smoke.lean": "test", "CountCatcherChecker/SpecTest.lean": "test"}


def count_lines(text: str) -> int:
    return text.count("\n")  # as wc -l


def code_lines(spec: str) -> tuple[int, list[str]]:
    """Lines and files (relative to lean/) of one entry of CODE_ROLES."""
    path, _, part = spec.partition("#")
    files = [f for f in sorted(LEAN_DIR.glob(path))
             if str(f.relative_to(LEAN_DIR)) not in CODE_EXCLUDED]
    if not files:
        raise FileNotFoundError(f"no Lean file for {spec}")
    rel = [str(f.relative_to(LEAN_DIR)) for f in files]
    if not part:
        return sum(count_lines(f.read_text()) for f in files), rel
    ls = files[0].read_text().splitlines(keepends=True)
    a = next(i for i, x in enumerate(ls) if x.startswith("/-! ## Parsing"))
    b = next(i for i, x in enumerate(ls) if x.startswith("/-! ## Checking and counting"))
    inside = count_lines("".join(ls[a:b]))
    return (inside if part == "parse" else count_lines("".join(ls)) - inside), rel


def lrat_closure() -> list[Path]:
    """The lrat-catcher modules that the sources import, closed under their imports."""
    imp = re.compile(r"^import (LRATCatcher(?:\.\w+)*)\s*$", re.M)
    roots = set()
    for f in [*LEAN_DIR.glob("CountCatcherChecker/**/*.lean"), *LEAN_DIR.glob("CountCatcherMath/**/*.lean"),
              LEAN_DIR / "CountCatcher.lean"]:
        if str(f.relative_to(LEAN_DIR)) not in CODE_EXCLUDED:
            roots.update(imp.findall(f.read_text()))
    seen: set[str] = set()
    todo = sorted(roots)
    while todo:
        mod = todo.pop()
        if mod in seen:
            continue
        seen.add(mod)
        todo.extend(imp.findall((LRAT_PKG / (mod.replace(".", "/") + ".lean")).read_text()))
    return [LRAT_PKG / (m.replace(".", "/") + ".lean") for m in sorted(seen)]


def app_code() -> None:
    lines = [APP_GEN + "% columns: role & lines (wc -l); group rows span the table; Pog.lean "
             "is split at its section headings into the parser and the validity check"]
    covered: set[str] = set()
    new_total = 0
    for gi, (group, roles) in enumerate(CODE_ROLES):
        if gi:
            lines.append("\\addlinespace")
        lines.append("\\multicolumn{2}{@{}l}{\\emph{" + group + "}} \\\\")
        for label, specs in roles:
            n = 0
            for spec in specs:
                k, rel = code_lines(spec)
                n += k
                covered.update(rel)
            new_total += n
            lines.append(f"\\quad {label} & {fmt_int(n)} \\\\")
    every = {str(f.relative_to(LEAN_DIR)) for d in ("CountCatcherChecker", "CountCatcherMath")
             for f in (LEAN_DIR / d).rglob("*.lean")}
    missing = every - covered - set(CODE_EXCLUDED)
    if missing:
        raise ValueError(f"Lean files without a role: {sorted(missing)}")
    lines.append("\\midrule")
    lines.append(f"New code, total & {fmt_int(new_total)} \\\\")
    if LRAT_PKG.exists():
        mods = lrat_closure()
        lines.append("Reused unchanged: lrat-catcher, the modules imported for the forward check"
                     f" & {fmt_int(sum(count_lines(m.read_text()) for m in mods))} \\\\")
    else:
        warn(f"appendix: {LRAT_PKG} missing, no line count for lrat-catcher")
    (TABLES / "app_code.tex").write_text("\n".join(lines) + "\n")


def code_families(em: Emitter) -> None:
    """Lean lines per family (wc -l), the hand-written effort that Section 5 names."""
    em.group("Lean lines of the family files (wc -l, encoder plus encoding lemma)",
             "lean/CountCatcherMath/Families/")
    for name, mods in (("famLatinLines", ["Latin", "LatinAll", "LatinCycle"]),
                       ("famKrewerasLines", ["Kreweras"])):
        n = sum(code_lines(f"CountCatcherMath/Families/{m}.lean")[0] for m in mods)
        em.add(name, fmt_int(n))


def write_appendix(em: Emitter, sc_rows: list[dict], r3inst: dict, r3: dict,
                   r4rows: list[dict], r4inst: dict) -> None:
    app_showcases(em, sc_rows)
    app_families()
    app_competition(r3inst, r3)
    app_miscount(em, r4rows, r4inst)
    app_adversarial()
    app_code()


# ---------------------------------------------------------------- output ---------------------
def header(em: Emitter) -> str:
    doc = __doc__.split("Conventions", 1)[1].split(":", 1)[1].strip()
    lines = ["% Generated by scripts/paper_numbers.py; do not edit by hand, rerun the script.",
             "% Requires \\PH (placeholder for values not yet in the data) defined by the paper.",
             "% Table bodies in PAPER/tables/ use these macros; include them inside tabular with",
             "% the primitive input (LaTeX's \\input breaks before \\bottomrule):",
             "%   \\makeatletter\\newcommand*{\\tablebody}[1]{\\@@input{#1}}\\makeatother",
             "% Conventions:"] + ["% " + ln for ln in doc.splitlines()]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- rerun of generation failures
RERUN_GEN_TSV = REPO / "research/eval-2026-10-11/rerun_gen.tsv"


def rerun_gen(em: Emitter, r3: dict) -> None:
    """The 26 formulas on which generation failed in R3, rerun on 2026-10-11 with a generation
    limit of 10,000 s in two modes (structural, and the hybrid with one SAT call per subgraph
    below tree size 10^6 as Bryant et al. describe it); report rerun_gen.md."""
    rows = list(csv.DictReader(io.StringIO(RERUN_GEN_TSV.read_text()), delimiter="\t"))
    em.group("Rerun of the generation failures (2026-10-11)", str(RERUN_GEN_TSV.relative_to(REPO)))
    forms = sorted({r["formula"] for r in rows})
    gen_ok = sorted({r["formula"] for r in rows if r["gen_exit"] == "0"})
    lean_std = {"results", "results_r2"}
    proved = sorted({r["formula"] for r in rows if r["status"] == "proved" and r["runset"] in lean_std})
    proved_any = sorted({r["formula"] for r in rows if r["status"] == "proved"})
    struct_ok = {r["formula"] for r in rows if r["gen_exit"] == "0" and r["mode"] == "struct"}
    hybrid_only = sorted({r["formula"] for r in rows
                          if r["gen_exit"] == "0" and r["mode"] == "hybrid"} - struct_ok)
    em.note("generation limit 10,000 s, Lean 3,600 s as in R3 (runsets results, results_r2); "
            "results_lean10k reruns Lean with 10,000 s; results128 is the 128 GB rerun")
    em.add("rgFailN", str(len(forms)))
    em.add("rgGenOk", str(len(gen_ok)))
    em.add("rgThm", str(len(proved)))
    em.add("rgThmLeanTenK", str(len(proved_any)))
    em.add("rgHybridOnly", str(len(hybrid_only)))
    em.add("rgTotal", str(int(em.values["funProved"]) + len(proved)))
    em.note("generated: " + ", ".join(gen_ok) + "; theorems at Lean 3,600 s: " + ", ".join(proved))


def write_numbers(em: Emitter) -> None:
    NUMBERS_TEX.parent.mkdir(parents=True, exist_ok=True)
    tail = ["", "% ---- values still \\PH (not yet in the data)"]
    for name, sofar, why in em.pending:
        tail.append(f"% \\{name}: {why}" + (f" (so far {sofar})" if sofar is not None else ""))
    NUMBERS_TEX.write_text(header(em) + "\n".join(em.lines) + "\n" + "\n".join(tail) + "\n")


def main() -> None:
    quiet = "--quiet" in sys.argv
    em = Emitter()
    r3src, r3inst = r3_load()
    r3 = r3_funnel(em, r3src, r3inst)
    r3_medians(em, r3inst, r3)
    write_numbers(em)  # partial results survive an interruption
    r4src, r4inst = r4_load()
    rows = r4_rows(r4inst)
    r4 = r4_macros(em, r4src, rows, r3, r3inst)
    write_fig3_csv(rows)
    write_numbers(em)
    abl_reverse_half(em, rows)
    abl_partc(em)
    abl_r5(em)
    abl_hybrid(em)
    abl_embed(em)
    kernel_only(em)
    unshortened(em)
    rerun_gen(em, r3)
    write_numbers(em)
    sc_rows = showcases(em)
    families(em)
    code_families(em)
    write_numbers(em)
    write_tables(em, sc_rows)
    write_appendix(em, sc_rows, r3inst, r3, rows, r4inst)
    write_numbers(em)  # the appendix writers add the miscount macros
    if not quiet:
        print(f"wrote {NUMBERS_TEX.relative_to(REPO)}: {len(em.names)} macros, "
              f"{len(em.pending)} \\PH")
        for w in WARNINGS:
            print("warning:", w)


if __name__ == "__main__":
    main()

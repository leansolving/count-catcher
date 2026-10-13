"""End-to-end driver: Lean encoder term (or DIMACS file) to a Lean theorem via `count_models`.

Steps, all local (small instances run on a laptop):
  1. export   the CNF from Lean with `#export_cnf` (header = the theorem's universe V, clauses
              in the order of the Lean term, so certificate clause IDs match it); a DIMACS file
              is copied instead
  2. count    D4 (-dDNNF): the model count (a cross-check only) and the decision-DNNF
  3a. N > 0   cpog-gen-fwd -F -T 500 -G (forward half only; it calls cadical and
              drat-trim) writes the CPOG certificate; the native
              translator cpog2lrat writes fwd.pog (node table) and fwd.lrat (part B refutation)
  3b. N = 0   cpog-gen refuses unsatisfiable formulas; CaDiCaL writes an LRAT refutation of the
              formula (tautological clauses left out, as Lean core's LRAT checker numbers them)
  4. theorem  NAME.lean: `count_models NAME … "fwd.pog" "fwd.lrat" (count := N)` (or the
              refutation) and `#print axioms NAME`; N is D4's count as a hint, which saves the
              command's elaboration-time part-A pass and is verified like any count (a wrong
              hint is rejected); with --no-hint the command computes N itself
  5. --run    Lean on NAME.lean with the precompiled checker loaded as a plugin; if a wrong
              hint is rejected, the file is rewritten without the hint and Lean runs again

Usage:
  uv run scripts/count_catcher.py NAME --via 'Domino.card_of_check (R := 8) (C := 8)' --run
  uv run scripts/count_catcher.py NAME --cnf 'Queens.cnf 8' [--universe 64] --run
  uv run scripts/count_catcher.py NAME --dimacs FILE.cnf --run
Options:
  --dir DIR        output directory (default count-catcher-out/NAME)
  --mode M         auto (default: the command decides by LRAT size), embed, stream
  --import MOD     Lean imports (default CountCatcher; repeatable)
  --open NS        namespaces to open (default CountCatcher SimpleGraph; repeatable)
  --no-hint        no count hint (the command runs part A to get the count)
  --no-delete      no deletions in fwd.lrat (default: cpog2lrat --delete)
  --no-trim        all additions in fwd.lrat and no keep file (default: cpog2lrat --trim, only
                   those the empty clause depends on)
  --inline         cpog2lrat --inline: single-use additions inlined into their consumer, also
                   for an embedded proof (not with --no-trim)
  --no-inline      no inlining; by default it is on wherever the proof is streamed (--mode
                   stream, and the second translation in auto mode) and off for embedded proofs
  --gen G          certificate generation: struct (default, structural), mono (cpog-gen -m),
                   hybrid (-M, -W: small subgraphs by one SAT call; gen_race.py), or race
                   (structural against --gen-race at once on two cores, the first wins)
  --gen-race C     the race's contender: hybrid (default) or mono
  --keep           keep in.nnf and cert.cpog
  --build          run `lake build CountCatcher` first (waits while another lake runs)
Streamed proofs load only the initial clauses that the LRAT cites: with --mode stream the
translator runs with --keep --binary --inline and the command gets (keep := "fwd.keep"). In
auto mode count_models streams a text LRAT file larger than countCatcher.embedMaxBytes (its
default, read from lean/CountCatcherMath/Command.lean): such a file is translated again with
--keep --binary --inline; smaller ones stay text and embedded. --mode embed: text, no keep file.
Tools: tools/bin (d4, the generator GEN_BIN, cadical, drat-trim, cpog2lrat) is put first on PATH.
"""

import argparse
import os
import platform
import re
import shutil
import subprocess
import sys
import time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(REPO, "lean")
TOOLS = os.path.join(REPO, "tools", "bin")
EXT = "dylib" if platform.system() == "Darwin" else "so"
PLUGINS = [
    f"--plugin={LEAN}/.lake/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.{EXT}",
    f"--plugin={LEAN}/.lake/build/lib/libCountCatcher_CountCatcherChecker.{EXT}",
]
ENV = dict(os.environ, PATH=TOOLS + os.pathsep + os.environ.get("PATH", ""))
TIMES = []
GEN_BIN, GEN_FL = "cpog-gen-fwd", ["-F", "-T", "500", "-G"]  # the generator and its options


def die(msg):
    sys.exit(f"count-catcher: {msg}")


def embed_max_default():
    """count_models' default countCatcher.embedMaxBytes, from its register_option in Command.lean."""
    with open(os.path.join(LEAN, "CountCatcherMath", "Command.lean")) as f:
        m = re.search(r"register_option countCatcher\.embedMaxBytes : Nat := \{\s*defValue := (\d+)",
                      f.read())
    if not m:
        die("no default of countCatcher.embedMaxBytes in lean/CountCatcherMath/Command.lean")
    return int(m.group(1))


def run(step, cmd, cwd, out=None, ok=(0,)):
    """Run cmd, record its wall time, return (exit code, combined output)."""
    t = time.time()
    p = subprocess.run(cmd, cwd=cwd, env=ENV, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       text=True)
    TIMES.append((step, time.time() - t))
    if out:
        with open(out, "w") as f:
            f.write(p.stdout)
    if p.returncode not in ok:
        die(f"{step} failed (exit {p.returncode}):\n{p.stdout[-2000:]}")
    return p.returncode, p.stdout


def lean(step, path, cwd_out):
    """Lean on path inside the lean package, plugins loaded; output to cwd_out."""
    return run(step, ["lake", "env", "lean", *PLUGINS, path], LEAN, out=cwd_out, ok=(0, 1))


def header(imports, opens):
    return "\n".join([f"import {m}" for m in imports] + ["", f"open {' '.join(opens)}", ""])


def strip_tautologies(src, dst):
    """Copy a DIMACS file without tautological clauses (Lean core's LRAT checker drops them
    from the formula and numbers the rest by position)."""
    clauses, cur, nv = [], [], 0
    with open(src) as f:
        for line in f:
            t = line.split()
            if not t or t[0] in ("c", "p") or not re.match(r"-?\d", t[0]):
                if t and t[0] == "p":
                    nv = int(t[2])
                continue
            for x in map(int, t):
                if x == 0:
                    clauses.append(cur)
                    cur = []
                else:
                    cur.append(x)
    keep = [c for c in clauses if not any(-x in c for x in c)]
    with open(dst, "w") as f:
        f.write(f"p cnf {nv} {len(keep)}\n")
        for c in keep:
            f.write(" ".join(map(str, c)) + " 0\n")
    return len(clauses) - len(keep)


def wait_for_lake():
    while subprocess.run(["pgrep", "-x", "lake"], stdout=subprocess.DEVNULL).returncode == 0:
        print("count-catcher: another lake process runs, waiting", file=sys.stderr)
        time.sleep(10)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("name")
    src = ap.add_mutually_exclusive_group(required=True)
    src.add_argument("--cnf", help="Lean term of type CNF Nat")
    src.add_argument("--via", help="family lemma application, e.g. 'Queens.card_of_check (n := 8)'")
    src.add_argument("--dimacs", help="DIMACS file")
    ap.add_argument("--universe", help="universe size V for --cnf (default: largest variable + 1)")
    ap.add_argument("--dir")
    ap.add_argument("--mode", choices=["auto", "embed", "stream"], default="auto")
    ap.add_argument("--import", dest="imports", action="append")
    ap.add_argument("--open", dest="opens", action="append")
    ap.add_argument("--no-hint", action="store_true")
    ap.add_argument("--no-delete", action="store_true")
    ap.add_argument("--no-trim", action="store_true")
    ap.add_argument("--inline", action="store_true")
    ap.add_argument("--no-inline", action="store_true")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--gen", choices=["struct", "mono", "hybrid", "race"], default="struct")
    ap.add_argument("--gen-race", choices=["hybrid", "mono"], default="hybrid")
    ap.add_argument("--run", action="store_true")
    a = ap.parse_args()
    imports = a.imports or ["CountCatcher"]
    opens = a.opens or ["CountCatcher", "SimpleGraph"]
    d = os.path.abspath(a.dir or os.path.join("count-catcher-out", a.name))
    os.makedirs(d, exist_ok=True)
    if a.inline and a.no_trim:
        die("--inline implies trimming; drop --no-trim")
    for t in ("d4", GEN_BIN, "cadical", "drat-trim", "cpog2lrat"):
        if not shutil.which(t, path=ENV["PATH"]):
            die(f"{t} not found in {TOOLS} or on PATH")
    if a.build:
        wait_for_lake()
        run("lake build", ["lake", "build", "CountCatcher"], LEAN)
    elif not os.path.exists(os.path.join(LEAN, ".lake/build/lib/lean/CountCatcher.olean")):
        die("CountCatcher is not built; run `lake build CountCatcher` in lean/ or pass --build")

    # 1. export
    uni = f" (V := {a.universe})" if a.universe else ""
    if a.dimacs:
        cnf_name = a.name + ".cnf"
        shutil.copy(a.dimacs, os.path.join(d, cnf_name))
        shutil.copy(a.dimacs, os.path.join(d, "in.cnf"))
        subject = f'"{cnf_name}"'
    else:
        subject = f"via ({a.via})" if a.via else f"({a.cnf}){uni}"
        exp = os.path.join(d, "export.lean")
        with open(exp, "w") as f:
            f.write(header(imports, opens) + f'#export_cnf {subject} "in.cnf"\n')
        e, out = lean("export", exp, os.path.join(d, "export.out"))
        if e != 0 or "error" in out:
            die(f"export failed:\n{out[-2000:]}")
    with open(os.path.join(d, "in.cnf")) as f:
        hdr = next((l.split() for l in f if l.startswith("p")), None)
    print(f"count-catcher: CNF {hdr[2]} variables, {hdr[3]} clauses")

    # 2. count
    _, out = run("d4", ["d4", "in.cnf", "-dDNNF", "-out=in.nnf"], d, out=os.path.join(d, "d4.log"))
    m = re.search(r"^s (\d+)", out, re.M)
    if not m:
        die(f"no count in D4's output:\n{out[-1000:]}")
    n_d4 = int(m.group(1))
    print(f"count-catcher: D4 count {n_d4}")

    # 3. certificate
    if n_d4 == 0:
        k = strip_tautologies(os.path.join(d, "in.cnf"), os.path.join(d, "in_nt.cnf"))
        ver = subprocess.run(["cadical", "--version"], env=ENV, stdout=subprocess.PIPE,
                             text=True).stdout.strip()
        fl = ["--lrat", "--no-binary"] + (["--no-factor"] if int(ver.split(".")[0]) >= 3 else [])
        e, _ = run("cadical", ["cadical", "-q", *fl, "in_nt.cnf", "unsat.lrat"], d, ok=(10, 20))
        if e != 20:
            die("D4 counts 0 but CaDiCaL finds a model")
        files = ['"unsat.lrat"']
        print(f"count-catcher: count 0, CaDiCaL refutation ({k} tautological clauses left out)")
        lrat = "unsat.lrat"
    else:
        if a.gen == "race":
            from gen_race import race
            g = race(GEN_BIN, GEN_FL, os.path.join(d, "in.cnf"), os.path.join(d, "in.nnf"), d,
                     env=ENV, contender=a.gen_race)
            TIMES.append((f"{GEN_BIN} race ({g['winner'] or 'none'} won)", g["wall_s"]))
            if g["winner"] is None:
                die(f"{GEN_BIN} failed in both modes: {g['exit']} (log in gen.log)")
            print(f"count-catcher: generation race won by {g['winner']} in {g['wall_s']:.1f} s")
        else:
            from gen_race import mode_flags
            run(GEN_BIN, [GEN_BIN, *mode_flags(a.gen), *GEN_FL, "in.cnf", "in.nnf", "cert.cpog"],
                d, out=os.path.join(d, "gen.log"))
        fl = [] if a.no_delete else ["--delete"]
        mask = a.mode == "stream" and not a.no_trim
        fl += ["--keep"] if mask else ([] if a.no_trim else ["--trim"])
        fl += ["--binary"] if a.mode == "stream" else []
        fl += ["--inline"] if a.inline or (mask and not a.no_inline) else []
        run("cpog2lrat", ["cpog2lrat", "in.cnf", "cert.cpog", "fwd", *fl], d)
        if (a.mode == "auto" and not a.no_trim
                and os.path.getsize(os.path.join(d, "fwd.lrat")) > embed_max_default()):
            # count_models would stream this file: translate again for part B on the cited clauses
            mask = True
            fl = ([] if a.no_delete else ["--delete"]) + ["--keep", "--binary"]
            fl += [] if a.no_inline else ["--inline"]
            run("cpog2lrat --keep", ["cpog2lrat", "in.cnf", "cert.cpog", "fwd", *fl], d)
        for x in ["fwd.cnf"] + ([] if a.keep else ["in.nnf", "cert.cpog"]):
            if os.path.exists(os.path.join(d, x)):
                os.remove(os.path.join(d, x))
        files = ['"fwd.pog"', '"fwd.lrat"'] + (['(keep := "fwd.keep")'] if mask else [])
        lrat = "fwd.lrat"
    sz = os.path.getsize(os.path.join(d, lrat))

    # 4. theorem file
    mode = "" if a.mode == "auto" else f" +{a.mode}"
    thy = os.path.join(d, a.name + ".lean")

    def write(hint):
        h = f" (count := {n_d4})" if hint and n_d4 > 0 else ""
        with open(thy, "w") as f:
            f.write(header(imports, opens)
                    + f"count_models{mode} {a.name} {subject} {' '.join(files)}{h}\n\n"
                    + f"#print axioms {a.name}\n")

    write(not a.no_hint)
    print(f"count-catcher: wrote {thy} (LRAT {sz} bytes)")

    # 5. Lean
    if a.run:
        e, out = lean("lean", thy, os.path.join(d, "lean.out"))
        if e != 0 and "part A (count)" in out:
            print("count-catcher: the certificate's count differs from D4's hint; rerunning without it")
            write(False)
            e, out = lean("lean (no hint)", thy, os.path.join(d, "lean.out"))
        print(out.strip())
        m = re.search(rf"count_models \S*{re.escape(a.name)}: (\d+) models", out)
        if e != 0 or not m or "depends on axioms" not in out:
            die("Lean did not prove the theorem (output in lean.out)")
        n = int(m.group(1))
        print(f"count-catcher: theorem {a.name} proved, count {n}"
              + ("" if n == n_d4 else f" (D4 said {n_d4}: MISMATCH, the theorem is right)"))
    print("count-catcher: times " + ", ".join(f"{s} {t:.1f} s" for s, t in TIMES))


if __name__ == "__main__":
    main()

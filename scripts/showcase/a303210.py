"""A303210(n), total dominating sets of the n x n torus, as a Lean theorem
(CountCatcherMath/Families/TotalDom.lean).

Exports the CNF from the Lean encoder (#export_cnf via TotalDom.torus_card_of_check, so clause IDs
match the theorem), runs D4, cpog-gen-fwd -F -T 500 -G and the native cpog2lrat (helpers of
scripts/graph_orbits.py), writes the theorem file with one count_models (D4's count as hint,
embedded or streamed by LRAT size) and runs Lean with the precompiled checker as plugin.

Usage:
  uv run scripts/showcase/a303210.py --n 5 [--out DIR] [--work DIR] [--lean LEANDIR]
      [--tools TOOLSDIR] [--embed-max BYTES] [--keep] [--no-lean] [--export-only]
Results: OUT/result.txt (key=value, written as each step finishes), OUT/T.lean,
OUT/export.out, OUT/lean.out; step logs (d4.log, gen.log, c2l.log) in WORK.
"""

import argparse
import os
import platform
import re
import shutil
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.dirname(HERE), HERE]  # scripts/ in the repository, or a flat copy
from graph_orbits import EXT, REPO, RSS, certify, files_arg, run  # noqa: E402

# a(3..8) from the OEIS entry; a(9), a(10) new, D4, ganak and sharpSAT-TD agree (oeis_harvest.md)
M = {3: 334, 4: 33489, 5: 11343461, 6: 14511093444, 7: 67561889987621,
     8: 1157220349268282289, 9: 72691237364024529045028,
     10: 16751614615998096965673730489}


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--out")
    ap.add_argument("--work")
    ap.add_argument("--lean", default=os.path.join(REPO, "lean"))
    ap.add_argument("--tools", default=os.path.join(REPO, "tools", "bin"))
    ap.add_argument("--embed-max", type=int, default=64 << 20)
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--no-lean", action="store_true")
    ap.add_argument("--export-only", action="store_true", help="stop after #export_cnf (WORK/in.cnf)")
    a = ap.parse_args()
    n = a.n
    name = f"A303210_{n}"
    out = os.path.abspath(a.out or os.path.join("a303210", name))
    work = os.path.abspath(a.work or os.path.join(out, "work"))
    os.makedirs(out, exist_ok=True)
    os.makedirs(work, exist_ok=True)
    env = dict(os.environ, PATH=a.tools + os.pathsep + os.environ.get("PATH", ""))
    plugins = [
        f"--plugin={a.lean}/.lake/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.{EXT}",
        f"--plugin={a.lean}/.lake/build/lib/libCountCatcher_CountCatcherChecker.{EXT}"]
    kv = open(os.path.join(out, "result.txt"), "w")

    def put(k, v):
        kv.write(f"{k}={v}\n")
        kv.flush()

    put("n", n)
    put("host", platform.node())
    lemma = f"CountCatcher.TotalDom.torus_card_of_check (m := {n - 2})"

    # 1. export the CNF from the Lean encoder
    exp = os.path.join(work, "export.lean")
    with open(exp, "w") as f:
        f.write(f'import CountCatcher\n\n#export_cnf via ({lemma}) "{work}/in.cnf"\n')
    _, dt = run(["lake", "env", "lean", *plugins, exp], a.lean, os.path.join(out, "export.out"),
                env=env)
    put("export_s", f"{dt:.1f}")
    if a.export_only:
        return

    # 2. D4, cpog-gen-fwd -F -T 500 -G, cpog2lrat --delete --trim
    t0 = time.time()
    r = certify(work, env, embed_max=a.embed_max)
    put("certify_wall_s", f"{time.time() - t0:.1f}")
    for k in ("vars", "clauses", "count", "d4_s", "d4_mb", "gen_s", "gen_mb", "c2l_s",
              "cpog_bytes", "pog_bytes", "lrat_bytes"):
        v = r.get(k)
        put(k, f"{v:.2f}" if isinstance(v, float) else v)
    put("c2l_mb", f"{RSS[os.path.join(work, 'c2l.log')]:.0f}")
    if n in M and r["count"] != M[n]:
        put("status", "count_mismatch")
        sys.exit(f"D4 count {r['count']} differs from a({n}) = {M[n]}")

    # 3. theorem file
    thy = os.path.join(work, "T.lean")
    with open(thy, "w") as f:
        f.write("\n".join([
            "import CountCatcher", "", "open CountCatcher", "",
            f"set_option countCatcher.embedMaxBytes {a.embed_max}", "",
            f"/-- OEIS A303210({n}): total dominating sets of the {n} x {n} torus grid graph. -/",
            f'count_models {name} via ({lemma}) {files_arg(r, work)} (count := {r["count"]})',
            "",
            f"example : Nat.card {{S : Finset (Fin {n} × Fin {n}) //",
            f"    ∀ v, ∃ u ∈ S, (SimpleGraph.cycleGraph {n} □ SimpleGraph.cycleGraph {n}).Adj v u}} =",
            f"    {r['count']} :=",
            f"  {name}", "",
            f"#print axioms {name}", ""]))
    shutil.copy(thy, os.path.join(out, "T.lean"))
    if a.no_lean:
        return

    # 4. Lean
    e, dt = run(["lake", "env", "lean", *plugins, thy], a.lean, os.path.join(out, "lean.out"),
                ok=(0, 1), env=env)
    put("lean_exit", e)
    put("lean_s", f"{dt:.1f}")
    put("lean_peak_mb", f"{RSS[os.path.join(out, 'lean.out')]:.0f}")
    txt = open(os.path.join(out, "lean.out")).read()
    m = re.search(rf"count_models {name}: (.*)", txt)
    put("lean_summary", m.group(1) if m else "")
    proved = e == 0 and "error" not in txt and f"'{name}' depends on axioms" in txt
    put("status", "proved" if proved else "lean_fail")
    if proved and not a.keep:
        shutil.rmtree(work, ignore_errors=True)
        put("work_deleted", work)
    kv.close()


if __name__ == "__main__":
    main()

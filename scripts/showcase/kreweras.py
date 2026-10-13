"""A358391(n), antichains of the Kreweras lattice NC(n), as a Lean theorem
(CountCatcherMath/Families/Kreweras.lean).

Exports the CNF from the Lean encoder (#export_cnf via Kreweras.card_of_check, so clause IDs
match the theorem), runs D4, cpog-gen-fwd -F -T 500 -G and the native cpog2lrat (helpers of
scripts/graph_orbits.py), writes the theorem file with one count_models (D4's count as hint,
embedded or streamed by LRAT size) and runs Lean with the precompiled checker as plugin.

Usage:
  uv run scripts/showcase/kreweras.py --n 5 [--out DIR] [--work DIR] [--lean LEANDIR]
      [--tools TOOLSDIR] [--embed-max BYTES] [--keep] [--no-lean] [--fp]
--fp: the statement over Finpartition (Kreweras.Fp.card_of_check) instead of Setoid.
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

# A358391 (offset 1); a(6) from the harvest (D4, ganak, sharpSAT-TD, two encodings), not in the OEIS.
M = {1: 2, 2: 3, 3: 10, 4: 234, 5: 2342196, 6: 206103695057137712}


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
    ap.add_argument("--fp", action="store_true")
    a = ap.parse_args()
    n = a.n
    name = f"kreweras{n}" + ("fp" if a.fp else "")
    out = os.path.abspath(a.out or os.path.join("kreweras", name))
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
    lemma = f"CountCatcher.Kreweras.{'Fp.' if a.fp else ''}card_of_check (n := {n})"
    carrier = (f"Finpartition (Finset.univ : Finset (Fin {n}))" if a.fp else f"Setoid (Fin {n})")
    stmt = (f"Nat.card {{A : Set {{P : {carrier} // P.IsNoncrossing}} // "
            f"IsAntichain (· ≤ ·) A}}")

    # 1. export the CNF from the Lean encoder
    exp = os.path.join(work, "export.lean")
    with open(exp, "w") as f:
        f.write(f'import CountCatcher\n\n#export_cnf via ({lemma}) "{work}/in.cnf"\n')
    _, dt = run(["lake", "env", "lean", *plugins, exp], a.lean, os.path.join(out, "export.out"),
                env=env)
    put("export_s", f"{dt:.1f}")

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
        sys.exit(f"D4 count {r['count']} differs from A358391({n}) = {M[n]}")

    # 3. theorem file
    thy = os.path.join(work, "T.lean")
    with open(thy, "w") as f:
        f.write("\n".join([
            "import CountCatcher", "", "open CountCatcher", "",
            f"set_option countCatcher.embedMaxBytes {a.embed_max}", "",
            f"/-- A358391({n}): antichains of the Kreweras lattice NC({n}). -/",
            f'count_models {name} via ({lemma}) {files_arg(r, work)} (count := {r["count"]})',
            "",
            f"example : {stmt} = {r['count']} :=",
            f"  {name}", "",
            f"#print axioms {name}", ""] + ([
            "/-- The same count over `Setoid`, from the same theorem (no second check). -/",
            f"theorem {name}_setoid : Nat.card {{A : Set {{r : Setoid (Fin {n}) // r.IsNoncrossing}} //",
            f"    IsAntichain (· ≤ ·) A}} = {r['count']} := by",
            f"  rw [CountCatcher.Kreweras.card_eq_card_fp]; exact {name}", "",
            f"#print axioms {name}_setoid", ""] if a.fp else [])))
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

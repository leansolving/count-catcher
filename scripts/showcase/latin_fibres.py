"""Reduced Latin squares of order n as a Lean theorem, split by the second row
(CountCatcherMath/Families/Latin.lean).

For every admissible second row r (a permutation of 0..n-1 with r[0] = 1 and r[j] != j, in the
lexicographic order of Latin.rows n) the fibre formula Latin.fibreCnf n r is exported from the
Lean term (#export_cnf via Latin.fibre_card_of_check, so clause IDs match the theorem), counted
by D4 and certified by cpog-gen-fwd -F -T 500 -G and the native cpog2lrat (helpers of
scripts/graph_orbits.py). The fibres are grouped into shards: a shard is one Lean module with one
count_models per fibre (D4's count as hint; embedded or streamed by LRAT size), compiled to an
.olean with the precompiled checker as plugin; its certificates are deleted once it is proved.
The assembly file imports all shards and proves Nat.card {L // IsReducedLatin L} = N with
Latin.card_eq_of_rows (row list against Latin.rows n and the sum by decide +kernel).

Usage:
  uv run scripts/showcase/latin_fibres.py --n 6 [--out DIR] [--work DIR] [--lean LEANDIR]
      [--tools TOOLSDIR] [--shard-size K] [--workers W] [--cert-j C] [--embed-max BYTES]
      [--keep] [--only-export] [--no-lean] [--fibres I,J,...]
W shard workers run at once; each certifies its fibres C at a time, then compiles its shard.
Results: OUT/result.txt (key=value), OUT/fibres.tsv (one row per fibre), OUT/T.lean,
OUT/lean.out, OUT/shards/S*.lean and S*.out. Shard modules and oleans live in WORK/mod.
"""

import argparse
import concurrent.futures as cf
import itertools
import os
import platform
import re
import shutil
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.dirname(HERE), HERE]  # scripts/ in the repository, or a flat copy
from graph_orbits import EXT, REPO, RSS, certify, files_arg, run  # noqa: E402

REDUCED = {2: 1, 3: 1, 4: 4, 5: 56, 6: 9408, 7: 16942080, 8: 535281401856}
HEADER = ["import CountCatcherMath.Command", "import CountCatcherMath.Families.Latin", "",
          "open CountCatcher", ""]


def admissible_rows(n):
    """Second rows of reduced squares, in the order of Latin.rows n (lexicographic)."""
    return [p for p in itertools.permutations(range(n))
            if p[0] == 1 and all(p[j] != j for j in range(n))]


def vec(p):
    return "![" + ", ".join(map(str, p)) + "]"


def chain(facts):
    c = "List.forall_mem_nil _"
    for f in reversed(facts):
        c = f"List.forall_mem_cons.2 ⟨{f},\n      {c}⟩"
    return c


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--out")
    ap.add_argument("--work")
    ap.add_argument("--lean", default=os.path.join(REPO, "lean"))
    ap.add_argument("--tools", default=os.path.join(REPO, "tools", "bin"))
    ap.add_argument("--shard-size", type=int, default=10)
    ap.add_argument("--workers", type=int, default=4, help="shards processed at once")
    ap.add_argument("--cert-j", type=int, default=1, help="certificates at once per shard")
    ap.add_argument("--embed-max", type=int, default=64 << 20)
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--only-export", action="store_true")
    ap.add_argument("--no-lean", action="store_true")
    a = ap.parse_args()
    n = a.n
    P = f"latin{n}"
    out = os.path.abspath(a.out or os.path.join("latin", P))
    work = os.path.abspath(a.work or os.path.join(out, "work"))
    mod = os.path.join(work, "mod")
    pkg = f"Latin{n}Fib"
    for d in (out, work, os.path.join(mod, pkg), os.path.join(out, "shards")):
        os.makedirs(d, exist_ok=True)
    env = dict(os.environ, PATH=a.tools + os.pathsep + os.environ.get("PATH", ""),
               LEAN_PATH=mod)
    plugins = [
        f"--plugin={a.lean}/.lake/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.{EXT}",
        f"--plugin={a.lean}/.lake/build/lib/libCountCatcher_CountCatcherChecker.{EXT}"]
    kv = open(os.path.join(out, "result.txt"), "w")
    lock = threading.Lock()

    def put(k, v):
        with lock:
            kv.write(f"{k}={v}\n")
            kv.flush()

    rows = admissible_rows(n)
    put("n", n)
    put("host", platform.node())
    put("fibres", len(rows))
    fdir = lambda i: os.path.join(work, f"f{i:03d}")
    thm = lambda i: f"{P}_r{i:03d}"
    lemma = lambda i: f"Latin.fibre_card_of_check (n := {n}) (r := {vec(rows[i])})"
    for i in range(len(rows)):
        os.makedirs(fdir(i), exist_ok=True)

    # 1. export every fibre formula from the Lean term, in one Lean run
    exp = os.path.join(work, "export.lean")
    with open(exp, "w") as f:
        f.write("\n".join(HEADER) + "\n")
        for i in range(len(rows)):
            f.write(f'#export_cnf via ({lemma(i)}) "{fdir(i)}/in.cnf"\n')
    _, dt = run(["lake", "env", "lean", *plugins, exp], a.lean, os.path.join(out, "export.out"),
                env=env)
    put("export_s", f"{dt:.1f}")
    put("export_peak_mb", f"{RSS[os.path.join(out, 'export.out')]:.0f}")
    if a.only_export:
        return

    # 2. shards: certificates, then one Lean module per shard, then delete the certificates
    shards = [list(range(s, min(s + a.shard_size, len(rows))))
              for s in range(0, len(rows), a.shard_size)]
    put("shards", len(shards))
    res, lean_info, shard_stat = {}, {}, {}
    stop = threading.Event()  # set by the first failed shard: the shards not yet started are skipped

    def do_shard(si):
        idxs = shards[si]
        if stop.is_set():
            raise RuntimeError("skipped after an earlier failure")
        t0 = time.time()
        try:
            with cf.ThreadPoolExecutor(max_workers=a.cert_j) as ex:
                rs = list(ex.map(lambda i: certify(fdir(i), env, embed_max=a.embed_max), idxs))
        except Exception:
            stop.set()
            raise
        tc = time.time() - t0
        for i, r in zip(idxs, rs):
            r["c2l_mb"] = RSS.get(os.path.join(fdir(i), "c2l.log"), 0)
            res[i] = r
        print(f"latin_fibres: shard {si}: {len(idxs)} certificates in {tc:.1f} s, counts "
              f"{sum(r['count'] for r in rs)}", flush=True)
        if a.no_lean:
            return
        src = os.path.join(mod, pkg, f"S{si:02d}.lean")
        lines = HEADER + [f"set_option countCatcher.embedMaxBytes {a.embed_max}", ""]
        for i in idxs:
            r = res[i]
            hint = f" (count := {r['count']})" if r["count"] > 0 else ""
            lines.append(f"count_models {thm(i)} via ({lemma(i)}) {files_arg(r)}{hint}")
        with open(src, "w") as f:
            f.write("\n".join(lines) + "\n")
        shutil.copy(src, os.path.join(out, "shards", f"S{si:02d}.lean"))
        log = os.path.join(out, "shards", f"S{si:02d}.out")
        e, dl = run(["lake", "env", "lean", *plugins, "-R", mod,
                     "-o", os.path.join(mod, pkg, f"S{si:02d}.olean"), src], a.lean, log,
                    ok=(0, 1), env=env)
        txt = open(log).read()
        ok = e == 0 and "error" not in txt
        for m in re.finditer(r"count_models (\S+): (.*)", txt):
            lean_info[m.group(1)] = m.group(2)
        shard_stat[si] = (tc, dl, RSS[log], ok)
        put(f"shard_{si:02d}", f"cert_s={tc:.1f} lean_s={dl:.1f} lean_peak_mb={RSS[log]:.0f} "
            f"ok={int(ok)}")
        if not ok:
            stop.set()
            raise RuntimeError(f"shard {si}: Lean failed, see {log}")
        if not a.keep:
            for i in idxs:
                shutil.rmtree(fdir(i), ignore_errors=True)

    t0 = time.time()
    failed = []
    with cf.ThreadPoolExecutor(max_workers=a.workers) as ex:
        futs = {ex.submit(do_shard, si): si for si in range(len(shards))}
        for fu in cf.as_completed(futs):
            try:
                fu.result()
            except Exception as err:  # keep going; the shard's certificates stay on disk
                failed.append(futs[fu])
                print(f"latin_fibres: shard {futs[fu]} failed: {err}", flush=True)
    put("shards_wall_s", f"{time.time() - t0:.1f}")
    total = sum(res[i]["count"] for i in res)
    put("count", total)
    if n in REDUCED and len(res) == len(rows) and total != REDUCED[n]:
        print(f"latin_fibres: count {total} differs from {REDUCED[n]}", flush=True)
    for k in ("d4_s", "gen_s", "c2l_s"):
        put(f"sum_{k}", f"{sum(r.get(k, 0) for r in res.values()):.1f}")
    for k in ("cpog_bytes", "lrat_bytes", "pog_bytes"):
        put(f"sum_{k}", sum(r.get(k, 0) for r in res.values()))
    for k in ("d4_mb", "gen_mb", "c2l_mb"):
        put(f"max_{k}", f"{max((r.get(k, 0) for r in res.values()), default=0):.0f}")
    if shard_stat:
        put("sum_shard_lean_s", f"{sum(s[1] for s in shard_stat.values()):.1f}")
        put("max_shard_lean_peak_mb", f"{max(s[2] for s in shard_stat.values()):.0f}")

    # per-fibre table
    with open(os.path.join(out, "fibres.tsv"), "w") as f:
        f.write("idx\trow\tcount\tkind\tvars\tclauses\td4_s\tgen_s\tc2l_s\tcpog_bytes\tlrat_bytes"
                "\tpog_bytes\td4_mb\tgen_mb\tc2l_mb\tlean\n")
        for i in sorted(res):
            r = res[i]
            f.write("\t".join(str(x) for x in [
                i, "".join(map(str, rows[i])), r["count"], r["kind"], r["vars"], r["clauses"],
                f"{r['d4_s']:.2f}", f"{r['gen_s']:.2f}", f"{r.get('c2l_s', 0):.2f}",
                r.get("cpog_bytes", 0), r["lrat_bytes"], r.get("pog_bytes", 0),
                f"{r['d4_mb']:.0f}", f"{r.get('gen_mb', 0):.0f}", f"{r.get('c2l_mb', 0):.0f}",
                lean_info.get(thm(i), "")]) + "\n")
    if failed or a.no_lean:
        put("status", f"failed_shards={sorted(failed)}" if failed else "no_lean")
        kv.close()
        return

    # 3. assembly
    N = total
    entries = [f"({vec(rows[i])}, {res[i]['count']})" for i in range(len(rows))]
    T = [*HEADER[:2], *(f"import {pkg}.S{si:02d}" for si in range(len(shards))), "",
         "open CountCatcher CountCatcher.Latin", "", "set_option maxRecDepth 100000", "",
         f"/-- The number of reduced Latin squares of order {n}, from {len(rows)} certified",
         "    counts, one per admissible second row (`Latin.card_eq_of_rows`). -/",
         f"theorem {P}_reduced :",
         f"    Nat.card {{L : Fin {n} → Fin {n} → Fin {n} // IsReducedLatin L}} = {N} :=",
         f"  Latin.card_eq_of_rows (n := {n}) (by norm_num) {N}",
         "    [" + ",\n     ".join(entries) + "]",
         f"    ({chain([thm(i) for i in range(len(rows))])})",
         "    (by decide +kernel)",
         "    (by decide +kernel)",
         "",
         f"#print axioms {P}_reduced"]
    thy = os.path.join(mod, "T.lean")
    with open(thy, "w") as f:
        f.write("\n".join(T) + "\n")
    shutil.copy(thy, os.path.join(out, "T.lean"))
    e, dt = run(["lake", "env", "lean", *plugins, thy], a.lean, os.path.join(out, "lean.out"),
                ok=(0, 1), env=env)
    put("asm_exit", e)
    put("asm_s", f"{dt:.1f}")
    put("asm_peak_mb", f"{RSS[os.path.join(out, 'lean.out')]:.0f}")
    txt = open(os.path.join(out, "lean.out")).read()
    proved = e == 0 and "error" not in txt and f"'{P}_reduced' depends on axioms" in txt
    put("status", "proved" if proved else "lean_fail")
    m = re.search(r"depends on axioms: \[(.*?)\]", txt, re.S)
    if m:
        ax = [x.strip() for x in m.group(1).split(",")]
        put("axioms_total", len(ax))
        put("axioms_native", sum(1 for x in ax if "native" in x))
        put("axioms_sorry", sum(1 for x in ax if "sorry" in x))
    kv.close()


if __name__ == "__main__":
    main()

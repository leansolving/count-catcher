# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Dedekind number M(n + 2) as a Lean theorem by the classes of the lower corner
(CountCatcherMath/Families/DedekindCorner.lean); the dress rehearsal of the M(8) run.

The monotone masks of D_n (2^n points, bit u = value at the point u) fall into S_n-classes; the
representative of a class is its smallest mask. Every class gets a leaf: the CNF
cube (Dedekind.cnf (n + 2)) (lits n r), whose models are the monotone functions on n + 2
variables with lower corner r. A plain leaf is one count_models theorem; a split leaf is a
SplitTree whose sub-cubes fix f10 and f01 (points u + 2^n and u + 2^(n+1)) at three maximal
free points of r per level, the all-ones cube refined again at the next level (the pilot's
recipe). The side checks (each representative monotone, smallest in its orbit, orbit
size times stabiliser = n!) run as decide +kernel per chunk of classes; the assembly is
DedekindCorner.card_eq_of_classes with the certified count of Dedekind.cnf n.

Pipeline per leaf: CNF written here in the clause order of the Lean term (checked against
#export_cnf with --check-export), D4, cpog-gen-fwd -F -T 500 -G, native cpog2lrat (helpers of
scripts/graph_orbits.py: --delete --trim, streamed leaves --keep --binary --inline). Leaves are
grouped into shards, one Lean module each with several count_models, compiled to an .olean with
the precompiled checker as plugin; certificates are deleted once their shard is proved.

Usage:
  uv run scripts/showcase/dedekind_corner.py --n 5 [--out DIR] [--work DIR] [--lean LEANDIR]
      [--tools TOOLSDIR] [--split CLASS:LEVELS,...] [--split-pts K] [--split-file JSON]
      [--shard-size K] [--workers W] [--cert-j C] [--chunk-size R] [--embed-max BYTES]
      [--check-export K] [--keep] [--only-side] [--side-limit K] [--mock PILOTDIR]
      [--emit-test DIR] [--no-lean]
--split CLASS:LEVELS splits the class with that index (in rep order) LEVELS levels deep with
--split-pts greedy maximal free points per level; --split-file gives the points explicitly.
--mock writes sorry leaf theorems with the pilot's D4 counts instead of certificates (to measure
the modules and the assembly at full size); --emit-test writes the whole run as one test file
with its certificates (lean/test conventions). Cluster job: scripts/cluster/ded_corner.sbatch.
Results: OUT/result.txt (key=value), OUT/classes.tsv, OUT/leaves.tsv, OUT/side.tsv,
OUT/T.lean, OUT/lean.out, OUT/mod/ (copies of the generated modules and their outputs).
Modules and oleans live in WORK/mod/<Pkg>.
"""

import argparse
import concurrent.futures as cf
import itertools
import math
import os
import platform
import re
import shutil
import sys
import threading
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.dirname(HERE), HERE]  # scripts/ in the repository, or a flat copy
from graph_orbits import EXT, REPO, RSS, certify, files_arg, run  # noqa: E402

M = {0: 2, 1: 3, 2: 6, 3: 20, 4: 168, 5: 7581, 6: 7828354, 7: 2414682040998,
     8: 56130437228687557907788}
NS = "CountCatcher.DedekindCorner"


# ---------------------------------------------------------------- classes, walk, tables

def dedekind_masks(n):
    """Sorted array of the monotone functions on n variables as 2^n-bit masks (n <= 6)."""
    d = np.array([0, 1], dtype=np.uint64)
    for k in range(n):
        shift = np.uint64(1 << k)
        out = []
        for f0 in d:
            f1 = d[(f0 & ~d) == 0]          # f0 <= f1 pointwise
            out.append(f0 | (f1 << shift))
        d = np.sort(np.concatenate(out))
        assert len(d) == M[k + 1], (k + 1, len(d))
    return d


def point_maps(n):
    """For every permutation of the n coordinates, the induced map on the 2^n points."""
    return np.array([[sum(((y >> i) & 1) << p[i] for i in range(n)) for y in range(1 << n)]
                     for p in itertools.permutations(range(n))], dtype=np.uint64)


def classes(n):
    """(rep, orbit size) per S_n-class of D_n, rep the smallest mask, sorted by rep."""
    d = dedekind_masks(n)
    weights = np.uint64(1) << point_maps(n)
    seen = np.zeros(len(d), dtype=bool)
    out = []
    for i in range(len(d)):
        if seen[i]:
            continue
        f = int(d[i])
        bits = np.array([(f >> y) & 1 for y in range(1 << n)], dtype=np.uint64)
        imgs = np.unique((weights * bits).sum(axis=1))
        idx = np.searchsorted(d, imgs)
        assert np.array_equal(d[idx], imgs) and not seen[idx].any()
        seen[idx] = True
        assert int(imgs[0]) == f  # d is sorted and f is the first unseen element
        out.append((f, len(imgs)))
    assert seen.all() and sum(o for _, o in out) == M[n]
    return out


def sjt_swaps(n):
    """Steinhaus-Johnson-Trotter: positions j of the n! - 1 adjacent swaps (j, j + 1)."""
    perm, dirs, out = list(range(n)), [-1] * n, []
    while True:
        mob, mpos = -1, -1
        for i, v in enumerate(perm):
            k = i + dirs[v]
            if 0 <= k < n and perm[k] < v and v > mob:
                mob, mpos = v, i
        if mob < 0:
            return out
        k = mpos + dirs[mob]
        perm[mpos], perm[k] = perm[k], perm[mpos]
        out.append(min(mpos, k))
        for v in range(mob + 1, n):
            dirs[v] = -dirs[v]


def walk(n):
    """The walk of DedekindCorner.pathOk: left multiplication by (j, j + 1) visits all n!."""
    path = sjt_swaps(n)
    vals, seen = list(range(n)), set()
    seen.add(tuple(vals))
    for j in path:
        vals = [j + 1 if v == j else j if v == j + 1 else v for v in vals]
        assert tuple(vals) not in seen
        seen.add(tuple(vals))
    assert len(seen) == math.factorial(n)
    return path


def swap_table(n):
    """(2^j, mask of the points with bit j set and bit j + 1 clear), j < n - 1."""
    return [(1 << j, sum(1 << u for u in range(1 << n) if (u >> j) & 1 and not (u >> (j + 1)) & 1))
            for j in range(n - 1)]


def mono_table(n):
    """(2^b, mask of the points with bit b clear), b < n."""
    return [(1 << b, sum(1 << u for u in range(1 << n) if not (u >> b) & 1)) for b in range(n)]


def delta_swap(s, M_, m):
    d = ((m >> s) ^ m) & M_
    return m ^ d ^ (d << s)


def side_check_py(n, reps, T, path):
    """The Lean side check repOk, simulated: smallest in the orbit, o * |Stab| = n!."""
    f = math.factorial(n)
    for r, o in reps:
        t, stab = r, 1
        for j in path:
            t = delta_swap(T[j][0], T[j][1], t)
            assert t >= r, (r, t)
            stab += t == r
        assert o * stab == f, (r, o, stab)


# ---------------------------------------------------------------- leaves and splits

def maximal_free(n, a, used):
    """Points u < 2^n with a(u) = 0, not in used, maximal among those (no free point above
    them), by decreasing popcount and value."""
    free = [u for u in range(1 << n) if not (a >> u) & 1 and u not in used]
    fs = set(free)
    mx = [u for u in free if not any((u | (1 << b)) in fs for b in range(n) if not (u >> b) & 1)]
    return sorted(mx, key=lambda u: (-bin(u).count("1"), -u))


def split_points(n, a, k=3):
    """Three points per level, greedy: maximal free points, refilled from the remaining free
    points (as the pilot: the bottom corner has only the top point as a maximal free point)."""
    used, pts = set(), []
    while len(pts) < k:
        mx = maximal_free(n, a, used)
        if not mx:
            break
        pts.append(mx[0])
        used.add(mx[0])
    return pts


def split_tree(n, a, levels, k=3, points=None):
    """The SplitTree of a split class: per level the variables f10 and f01 at k points (greedy
    maximal free points, or the given point lists), the all-ones cube refined at the next level.
    Returns (tree, leaves): tree as nested tuples ('node', x, pos, neg) / ('leaf', key); leaves
    as {key: literal list deepest first}."""
    used, levs = set(), []
    if points:
        levs = [[p + (1 << n) for p in pts] + [p + (2 << n) for p in pts] for pts in points]
    for _ in range(0 if points else levels):
        pts = []
        while len(pts) < k:
            mx = maximal_free(n, a, used)
            if not mx:
                break
            pts.append(mx[0])
            used.add(mx[0])
        levs.append([p + (1 << n) for p in pts] + [p + (2 << n) for p in pts])
    leaves = {}

    def build(lv, depth, lits):
        xs = levs[lv]
        if depth == len(xs):
            if lv + 1 < len(levs) and all(b for _, b in lits[:len(xs)]):
                return build(lv + 1, 0, lits)
            key = "".join("1" if b else "0" for _, b in reversed(lits))
            leaves[key] = list(lits)
            return ("leaf", key)
        x = xs[depth]
        return ("node", x, build(lv, depth + 1, [(x, True)] + lits),
                build(lv, depth + 1, [(x, False)] + lits))

    return build(0, 0, []), leaves


def tree_lean(t, name):
    """The SplitTree term (counts from cnt) and the Holds proof (leaf theorems by key)."""
    if t[0] == "leaf":
        return f"(SplitTree.leaf {name['cnt'][t[1]]})", f"(SplitTree.Holds.mk_leaf {name['thm'][t[1]]})"
    _, x, p, q = t
    tp, hp = tree_lean(p, name)
    tq, hq = tree_lean(q, name)
    return f"(SplitTree.node {x} {tp} {tq})", f"(SplitTree.Holds.mk_node {hp} {hq})"


def lits_lean(n, a, path_lits):
    s = f"lits {n} {a}"
    for x, b in reversed(path_lits):
        s = f"({x}, {'true' if b else 'false'}) :: " + s
    return s


def write_leaf_cnf(path, n, a, path_lits):
    """DIMACS of cube (Dedekind.cnf (n + 2)) (path_lits ++ lits n a), clauses in the order of
    the Lean term (Command.dimacs): the covering pairs (point u, then clear bit b), then the
    unit clauses in list order."""
    N = n + 2
    cl = []
    for u in range(1 << N):
        for b in range(N):
            if not (u >> b) & 1:
                cl.append(f"-{u + 1} {(u | (1 << b)) + 1} 0\n")
    for x, b in path_lits:
        cl.append(f"{x + 1 if b else -(x + 1)} 0\n")
    for u in range(1 << n):
        cl.append(f"{u + 1 if (a >> u) & 1 else -(u + 1)} 0\n")
    with open(path, "w") as f:
        f.write(f"p cnf {1 << N} {len(cl)}\n")
        f.writelines(cl)


def write_ded_cnf(path, n):
    """DIMACS of Dedekind.cnf n."""
    cl = [f"-{u + 1} {(u | (1 << b)) + 1} 0\n" for u in range(1 << n) for b in range(n)
          if not (u >> b) & 1]
    with open(path, "w") as f:
        f.write(f"p cnf {1 << n} {len(cl)}\n")
        f.writelines(cl)


def lean_list(xs, per_line=6, indent="  "):
    lines = []
    for i in range(0, len(xs), per_line):
        lines.append(indent + ", ".join(xs[i:i + per_line]))
    return "[\n" + ",\n".join(lines) + "]"


def chain_forall(facts):
    c = "List.forall_mem_nil _"
    for f in reversed(facts):
        c = f"List.forall_mem_cons.2 ⟨{f},\n    {c}⟩"
    return c


# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--n", type=int, required=True, help="inner variables; proves M(n + 2)")
    ap.add_argument("--out")
    ap.add_argument("--work")
    ap.add_argument("--lean", default=os.path.join(REPO, "lean"))
    ap.add_argument("--tools", default=os.path.join(REPO, "tools", "bin"))
    ap.add_argument("--split", default="", help="CLASS:LEVELS,... (class index in rep order)")
    ap.add_argument("--split-pts", type=int, default=3, help="points per split level")
    ap.add_argument("--split-file", help='JSON {"<rep mask>": [[points of level 1], [level 2], ...]}'
                    " (explicit split points, e.g. the pilot's recipe)")
    ap.add_argument("--shard-size", type=int, default=40)
    ap.add_argument("--workers", type=int, default=4, help="shards processed at once")
    ap.add_argument("--cert-j", type=int, default=1, help="certificates at once per shard")
    ap.add_argument("--chunk-size", type=int, default=50, help="classes per side-check chunk")
    ap.add_argument("--embed-max", type=int, default=1 << 20)
    ap.add_argument("--check-export", type=int, default=3,
                    help="leaves whose CNF is also exported by #export_cnf and compared")
    ap.add_argument("--side-limit", type=int, default=0,
                    help="run only the first K side-check chunks (measurement)")
    ap.add_argument("--emit-test", help="also write a single-file test (DIR/<Name>.lean, DIR/data)")
    ap.add_argument("--mock", help="pilot directory (classes.tsv, res/d4_*.tsv): no certificates, "
                    "the leaf theorems are sorry with the pilot's D4 counts (1 where missing), "
                    "to measure the modules and the assembly at full scale")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--only-side", action="store_true", help="data and side checks only")
    ap.add_argument("--no-lean", action="store_true")
    a = ap.parse_args()
    n, N = a.n, a.n + 2
    P = f"dedekind{N}c"
    pkg = f"Ded{N}C"
    out = os.path.abspath(a.out or os.path.join("dedekind_corner", P))
    work = os.path.abspath(a.work or os.path.join(out, "work"))
    mod = os.path.join(work, "mod")
    for d in (out, work, os.path.join(mod, pkg), os.path.join(out, "mod")):
        os.makedirs(d, exist_ok=True)
    env = dict(os.environ, PATH=a.tools + os.pathsep + os.environ.get("PATH", ""),
               LEAN_PATH=mod)
    plugins = [
        f"--plugin={a.lean}/.lake/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.{EXT}",
        f"--plugin={a.lean}/.lake/build/lib/libCountCatcher_CountCatcherChecker.{EXT}"]
    kv = open(os.path.join(out, "result.txt"), "a")
    lock = threading.Lock()

    def put(k, v):
        with lock:
            kv.write(f"{k}={v}\n")
            kv.flush()

    def lean_mod(name, lines):
        """Write WORK/mod/<pkg>/<name>.lean and compile it to an .olean; returns (ok, secs,
        peak MB, output text)."""
        src = os.path.join(mod, pkg, f"{name}.lean")
        with open(src, "w") as f:
            f.write("\n".join(lines) + "\n")
        shutil.copy(src, os.path.join(out, "mod", f"{name}.lean"))
        log = os.path.join(out, "mod", f"{name}.out")
        e, dt = run(["lake", "env", "lean", *plugins, "-R", mod,
                     "-o", os.path.join(mod, pkg, f"{name}.olean"), src], a.lean, log,
                    ok=(0, 1), env=env)
        txt = open(log).read()
        return e == 0 and "error" not in txt, dt, RSS[log], txt

    put("n", n)
    put("host", platform.node())
    put("start", time.strftime("%Y-%m-%d %H:%M:%S"))

    # 1. classes, walk, tables; the side check simulated
    t0 = time.time()
    cls = classes(n)
    path = walk(n)
    T, Ls = swap_table(n), mono_table(n)
    side_check_py(n, cls, T, path)
    put("classes", len(cls))
    put("classes_s", f"{time.time() - t0:.1f}")
    with open(os.path.join(out, "classes.tsv"), "w") as f:
        f.write("idx\tpopcount\torbit\trep\n")
        for i, (r, o) in enumerate(cls):
            f.write(f"{i}\t{bin(r).count('1')}\t{o}\t{r:#x}\n")
    chunks = [list(range(s, min(s + a.chunk_size, len(cls))))
              for s in range(0, len(cls), a.chunk_size)]
    put("chunks", len(chunks))
    mock = {}
    if a.mock:
        cid_rep = {}
        for line in open(os.path.join(a.mock, "classes.tsv")).read().splitlines()[1:]:
            cid, _, _, h = line.split("\t")
            cid_rep[cid] = int(h, 16)
        import glob
        for fn in glob.glob(os.path.join(a.mock, "res", "d4_*.tsv")):
            for line in open(fn).read().splitlines()[1:]:
                c = line.split("\t")
                if len(c) >= 7 and "_" not in c[0] and c[2] == "0" and c[6] and c[0] in cid_rep:
                    mock[cid_rep[c[0]]] = int(c[6])
        put("mock_counts", len(mock))

    # 2. data module and side-check chunks
    pairs = lambda idx: lean_list([f"({cls[i][0]}, {cls[i][1]})" for i in idx], 4, "    ")
    body = ["/-- Delta-swap table: shift and mask per adjacent transposition. -/",
            "def T : List (ℕ × ℕ) := " + lean_list([f"({s}, {m})" for s, m in T], 1, "    "),
            "/-- Monotonicity table: shift and mask per coordinate. -/",
            "def Ls : List (ℕ × ℕ) := " + lean_list([f"({s}, {m})" for s, m in Ls], 1, "    "),
            f"/-- The walk through all {math.factorial(n)} permutations (SJT). -/",
            "def P : List ℕ := " + lean_list([str(j) for j in path], 40, "    ")]
    checks = [f"theorem hT : tableOk {n} T = true := by decide +kernel",
              f"theorem hL : monoTableOk {n} Ls = true := by decide +kernel",
              f"theorem hP : pathOk {n} P = true := by decide +kernel", ""]
    qdefs = []
    for k, idx in enumerate(chunks):
        qdefs.append(f"/-- Classes {idx[0]} to {idx[-1]}: (representative, orbit size). -/")
        qdefs.append(f"def Q{k:03d} : List (ℕ × ℕ) := " + pairs(idx))
    chk_line = lambda k: (f"theorem chk{k:03d} : Q{k:03d}.all (repOk {n} T Ls P) = true := by "
                          "decide +kernel")
    data = [f"import CountCatcherMath.Families.DedekindCorner", "",
            f"/-! Side data of M({N}) by the classes of the lower corner "
            "(scripts/showcase/dedekind_corner.py). -/", "",
            f"open {NS}", "", f"namespace {pkg}", "", *body, "",
            "set_option profiler true", "set_option profiler.threshold 10", "", *checks,
            *qdefs, "", f"end {pkg}"]
    if a.no_lean:
        with open(os.path.join(out, "Data.lean"), "w") as f:
            f.write("\n".join(data) + "\n")
    else:
        ok, dt, mb, txt = lean_mod("Data", data)
        put("data_ok", int(ok))
        put("data_s", f"{dt:.1f}")
        prof = re.findall(r"(tactic execution of \S+|type checking|elaboration) took ([\d.]+)(m?s)", txt)
        put("data_profile", ";".join(f"{x}={v}{u}" for x, v, u in prof))
        if not ok:
            put("status", "data_fail")
            sys.exit(f"Data module failed, see {out}/mod/Data.out")

        side = {}

        def do_chunk(k):
            lines = [f"import {pkg}.Data", "", f"open {NS}", "", f"namespace {pkg}", "",
                     "set_option profiler true", "set_option profiler.threshold 10", "",
                     chk_line(k), "", f"end {pkg}"]
            ok, dt, mb, txt = lean_mod(f"Chk{k:03d}", lines)
            ms = sum(float(v) * (1 if u == "ms" else 1000) for v, u in
                     re.findall(r"took ([\d.]+)(m?s)", txt))
            side[k] = (ok, dt, mb, ms)
            if not ok:
                raise RuntimeError(f"side check chunk {k} failed")

        t0 = time.time()
        with cf.ThreadPoolExecutor(max_workers=a.workers) as ex:
            list(ex.map(do_chunk, range(min(len(chunks), a.side_limit or len(chunks)))))
        put("side_wall_s", f"{time.time() - t0:.1f}")
        with open(os.path.join(out, "side.tsv"), "w") as f:
            f.write("chunk\tclasses\tok\tlean_s\tpeak_mb\tprofiled_ms\n")
            for k in sorted(side):
                ok, dt, mb, ms = side[k]
                f.write(f"{k}\t{len(chunks[k])}\t{int(ok)}\t{dt:.1f}\t{mb:.0f}\t{ms:.0f}\n")
        put("side_sum_profiled_ms", f"{sum(s[3] for s in side.values()):.0f}")
        put("side_sum_lean_s", f"{sum(s[1] for s in side.values()):.1f}")
    if a.only_side:
        put("status", "side_only")
        return

    # 3. leaves: plan
    splits, split_pts = {}, {}
    for spec in filter(None, a.split.split(",")):
        c, lv = spec.split(":")
        splits[int(c)] = int(lv)
    if a.split_file:
        import json
        idx_of = {r: i for i, (r, _) in enumerate(cls)}
        for key, pts in json.load(open(a.split_file)).items():
            i = idx_of[int(key, 0)]
            splits[i], split_pts[i] = len(pts), pts
    leaves = []  # (key, class index, path literals deepest first)
    trees = {}
    for i, (r, o) in enumerate(cls):
        if i in splits:
            t, lv = split_tree(n, r, splits[i], a.split_pts, split_pts.get(i))
            trees[i] = t
            for key, pl in sorted(lv.items()):
                leaves.append((f"c{i:05d}_{key}", i, pl))
        else:
            leaves.append((f"c{i:05d}", i, []))
    put("leaves", len(leaves))
    put("split_classes", ";".join(f"{i}:{splits[i]}" for i in sorted(splits)))
    ldir = lambda key: os.path.join(work, "leaf", key)
    for key, i, pl in leaves if not a.mock else []:
        os.makedirs(ldir(key), exist_ok=True)
        write_leaf_cnf(os.path.join(ldir(key), "in.cnf"), n, cls[i][0], pl)
    lemma = lambda i, pl: f"{NS}.leaf_card_of_check (n := {n}) (ls := {lits_lean(n, cls[i][0], pl)})"

    # 3a. compare a few CNFs with the Lean export
    if a.check_export and not a.no_lean and not a.mock:
        sample = [leaves[0], leaves[-1]] + [l for l in leaves if l[2]][:max(0, a.check_export - 2)]
        exp = os.path.join(work, "export.lean")
        with open(exp, "w") as f:
            f.write(f"import CountCatcherMath.Command\nimport CountCatcherMath.Families.DedekindCorner\n\n"
                    f"open CountCatcher {NS}\n\n")
            for key, i, pl in sample:
                f.write(f'#export_cnf via ({lemma(i, pl)}) "{ldir(key)}/lean.cnf"\n')
        _, dt = run(["lake", "env", "lean", *plugins, exp], a.lean, os.path.join(out, "export.out"),
                    env=env)
        same = all(open(os.path.join(ldir(k), "in.cnf")).read() ==
                   open(os.path.join(ldir(k), "lean.cnf")).read() for k, _, _ in sample)
        put("export_check", f"{len(sample)} leaves, identical={int(same)}, {dt:.1f} s")
        if not same:
            sys.exit("the Python CNF differs from #export_cnf")

    # 3b. M(n): the certified count of Dedekind.cnf n
    mdir = os.path.join(work, "mn")
    os.makedirs(mdir, exist_ok=True)
    write_ded_cnf(os.path.join(mdir, "in.cnf"), n)
    rm = certify(mdir, env, embed_max=a.embed_max)
    put("mn_count", rm["count"])
    assert rm["count"] == M[n]
    if not a.no_lean:
        ok, dt, mb, txt = lean_mod("Mn", [
            "import CountCatcherMath.Command", "import CountCatcherMath.Families.Dedekind", "",
            "open CountCatcher", "",
            f"set_option countCatcher.embedMaxBytes {a.embed_max}", "",
            f"count_models {pkg}.dedekind{n} via (Dedekind.card_of_check (n := {n})) "
            f"{files_arg(rm)} (count := {rm['count']})"])
        put("mn", f"ok={int(ok)} lean_s={dt:.1f}")
        if not ok:
            sys.exit("Mn failed")

    # 4. shards: split classes get their own shards, plain leaves in shard-size groups
    shards = []
    plain = [l for l in leaves if not l[2] and l[1] not in splits]
    for s in range(0, len(plain), a.shard_size):
        shards.append(plain[s:s + a.shard_size])
    for i in sorted(splits):
        sub = [l for l in leaves if l[1] == i]
        for s in range(0, len(sub), a.shard_size):
            shards.append(sub[s:s + a.shard_size])
    put("shards", len(shards))
    res, lean_info, shard_stat, shard_of = {}, {}, {}, {}
    thm = lambda key: f"{pkg}.l_{key}"
    stop = threading.Event()

    def do_shard(si):
        group = shards[si]
        if stop.is_set():
            raise RuntimeError("skipped after an earlier failure")
        t0 = time.time()
        try:
            if a.mock:
                rs = [{"count": mock.get(cls[l[1]][0], 1) if not l[2] else 1, "kind": "mock",
                       "lrat_bytes": 0} for l in group]
            else:
                with cf.ThreadPoolExecutor(max_workers=a.cert_j) as ex:
                    rs = list(ex.map(lambda l: certify(ldir(l[0]), env, embed_max=a.embed_max),
                                     group))
        except Exception:
            stop.set()
            raise
        tc = time.time() - t0
        for l, r in zip(group, rs):
            r["c2l_mb"] = RSS.get(os.path.join(ldir(l[0]), "c2l.log"), 0)
            res[l[0]] = r
            shard_of[l[0]] = si
        if a.no_lean:
            return
        lines = ["import CountCatcherMath.Command", "import CountCatcherMath.Families.DedekindCorner",
                 "", f"open CountCatcher {NS}", "",
                 f"set_option countCatcher.embedMaxBytes {a.embed_max}", ""]
        for key, i, pl in group:
            r = res[key]
            if a.mock:
                lines.append(f"theorem {thm(key)} : Fintype.card {{x : Fin (2 ^ ({n} + 2)) → Bool //"
                             f" (cube (Dedekind.cnf ({n} + 2)) ({lits_lean(n, cls[i][0], pl)})).eval"
                             f" (ext x) = true}} = {r['count']} := sorry")
                continue
            hint = f" (count := {r['count']})" if r["count"] > 0 else ""
            lines.append(f"count_models {thm(key)} via ({lemma(i, pl)}) {files_arg(r)}{hint}")
        ok, dl, mb, txt = lean_mod(f"S{si:03d}", lines)
        for m_ in re.finditer(r"count_models (\S+): (.*)", txt):
            lean_info[m_.group(1)] = m_.group(2)
        shard_stat[si] = (tc, dl, mb, ok)
        put(f"shard_{si:03d}", f"leaves={len(group)} cert_s={tc:.1f} lean_s={dl:.1f} "
            f"lean_peak_mb={mb:.0f} ok={int(ok)}")
        if not ok:
            stop.set()
            raise RuntimeError(f"shard {si}: Lean failed, see {out}/mod/S{si:03d}.out")
        if not a.keep:
            for l in group:
                for x in ("fwd.pog", "fwd.lrat", "fwd.keep", "unsat.lrat"):
                    p_ = os.path.join(ldir(l[0]), x)
                    if os.path.exists(p_):
                        os.remove(p_)

    t0 = time.time()
    failed = []
    with cf.ThreadPoolExecutor(max_workers=a.workers) as ex:
        futs = {ex.submit(do_shard, si): si for si in range(len(shards))}
        for fu in cf.as_completed(futs):
            try:
                fu.result()
            except Exception as err:
                failed.append(futs[fu])
                print(f"dedekind_corner: shard {futs[fu]} failed: {err}", flush=True)
    put("shards_wall_s", f"{time.time() - t0:.1f}")
    for k in ("d4_s", "gen_s", "c2l_s"):
        put(f"sum_{k}", f"{sum(r.get(k, 0) for r in res.values()):.1f}")
        put(f"max_{k}", f"{max((r.get(k, 0) for r in res.values()), default=0):.2f}")
    for k in ("cpog_bytes", "lrat_bytes", "pog_bytes"):
        put(f"sum_{k}", sum(r.get(k, 0) for r in res.values()))
        put(f"max_{k}", max((r.get(k, 0) for r in res.values()), default=0))
    for k in ("d4_mb", "gen_mb", "c2l_mb"):
        put(f"max_{k}", f"{max((r.get(k, 0) for r in res.values()), default=0):.0f}")
    put("streamed_leaves", sum(1 for r in res.values() if r.get("keep")))
    if shard_stat:
        put("sum_shard_lean_s", f"{sum(s[1] for s in shard_stat.values()):.1f}")
        put("max_shard_lean_s", f"{max(s[1] for s in shard_stat.values()):.1f}")
        put("max_shard_lean_peak_mb", f"{max(s[2] for s in shard_stat.values()):.0f}")
    with open(os.path.join(out, "leaves.tsv"), "w") as f:
        f.write("key\tclass\tdepth\tcount\tkind\td4_s\tgen_s\tc2l_s\tcpog_bytes\tlrat_bytes"
                "\tpog_bytes\tstreamed\td4_mb\tgen_mb\tc2l_mb\tshard\tlean\n")
        for key, i, pl in leaves:
            r = res.get(key)
            if not r:
                continue
            f.write("\t".join(str(x) for x in [
                key, i, len(pl), r["count"], r["kind"], f"{r.get('d4_s', 0):.2f}",
                f"{r.get('gen_s', 0):.2f}", f"{r.get('c2l_s', 0):.2f}", r.get("cpog_bytes", 0),
                r["lrat_bytes"], r.get("pog_bytes", 0), int(bool(r.get("keep"))),
                f"{r.get('d4_mb', 0):.0f}", f"{r.get('gen_mb', 0):.0f}",
                f"{r.get('c2l_mb', 0):.0f}", shard_of.get(key, ""),
                lean_info.get(thm(key), "")]) + "\n")
    # class counts
    ccount = {}
    for key, i, pl in leaves:
        if key in res:
            ccount[i] = ccount.get(i, 0) + res[key]["count"]
    total = sum(cls[i][1] * ccount.get(i, 0) for i in range(len(cls)))
    put("weighted_sum", total)
    put("weighted_sum_ok", int(total == M[N]))
    if failed or a.no_lean:
        put("status", f"failed_shards={sorted(failed)}" if failed else "no_lean")
        return

    # 5. split classes: one module per class (imports the shards of its leaves)
    cls_thm, cls_body = {}, {}
    for i in sorted(splits):
        sub = [l for l in leaves if l[1] == i]
        names = {"cnt": {l[0].split("_", 1)[1]: res[l[0]]["count"] for l in sub},
                 "thm": {l[0].split("_", 1)[1]: thm(l[0]) for l in sub}}
        tt, hh = tree_lean(trees[i], names)
        sh = sorted({shard_of[l[0]] for l in sub})
        lines = ["import CountCatcherMath.Families.DedekindCorner",
                 *(f"import {pkg}.S{si:03d}" for si in sh), "",
                 f"open CountCatcher {NS}", "", "set_option maxRecDepth 100000", ""]
        cls_body[i] = [
            f"/-- Class {i} ({cls[i][0]:#x}), split into {len(sub)} sub-cubes. -/",
            f"theorem {pkg}.cls{i:05d} : leafCount {n} {cls[i][0]} = {ccount[i]} :=",
            f"  leafCount_of_tree (n := {n}) (m := {cls[i][0]}) {tt}",
            f"    {hh}", "    rfl"]
        ok, dt, mb, txt = lean_mod(f"K{i:05d}", lines + cls_body[i])
        put(f"class_{i:05d}", f"ok={int(ok)} lean_s={dt:.1f} leaves={len(sub)} count={ccount[i]}")
        if not ok:
            sys.exit(f"class module {i} failed")
        cls_thm[i] = f"{pkg}.cls{i:05d}"
    for key, i, pl in leaves:
        if i not in splits:
            cls_thm[i] = thm(key)

    # 6. assembly: chunk sums, card_eq_of_classes
    sums = {k: sum(cls[i][1] * ccount[i] for i in idx) for k, idx in enumerate(chunks)}
    Th = ["import CountCatcherMath.Command", "import CountCatcherMath.Families.DedekindCorner",
          f"import {pkg}.Data", f"import {pkg}.Mn",
          *(f"import {pkg}.Chk{k:03d}" for k in range(len(chunks))),
          *(f"import {pkg}.S{si:03d}" for si in range(len(shards))),
          *(f"import {pkg}.K{i:05d}" for i in sorted(splits)), "",
          f"open CountCatcher {NS}", "", "set_option maxRecDepth 100000", ""]
    Tl = []
    for k, idx in enumerate(chunks):
        ch = "chunkSum_nil"
        for i in reversed(idx):
            ch = f"chunkSum_cons (n := {n}) {cls_thm[i]}\n    ({ch})"
        Tl += [f"theorem {pkg}.sum{k:03d} :",
               f"    ({pkg}.Q{k:03d}.map fun p => p.2 * leafCount {n} p.1).sum = {sums[k]} :=",
               f"  Eq.trans ({ch}) (by decide +kernel)", ""]
    Ks = ", ".join(f"({pkg}.Q{k:03d}, {sums[k]})" for k in range(len(chunks)))
    Tl += [f"/-- The Dedekind number M({N}) by the {len(cls)} classes of the lower corner "
           f"(S_{n}-classes of D_{n}). -/",
           f"theorem {P} : Nat.card {{f : (Fin {N} → Bool) → Bool // Monotone f}} = "
           f"{total if a.mock else M[N]} :=",
           f"  (card_eq_of_classes {n} {pkg}.T {pkg}.Ls {pkg}.hT {pkg}.hL {pkg}.P {pkg}.hP",
           f"    [{Ks}]",
           f"    ({chain_forall([f'{pkg}.chk{k:03d}' for k in range(len(chunks))])})",
           "    (by decide +kernel)",
           f"    ({pkg}.dedekind{n}.trans (by decide +kernel))",
           f"    ({chain_forall([f'{pkg}.sum{k:03d}' for k in range(len(chunks))])})).trans",
           "    (by decide +kernel)", "",
           f"#print axioms {P}"]
    thy = os.path.join(mod, pkg, "T.lean")
    with open(thy, "w") as f:
        f.write("\n".join(Th + Tl) + "\n")
    shutil.copy(thy, os.path.join(out, "T.lean"))
    e, dt = run(["lake", "env", "lean", *plugins, thy], a.lean, os.path.join(out, "lean.out"),
                ok=(0, 1), env=env)
    put("asm_exit", e)
    put("asm_s", f"{dt:.1f}")
    put("asm_peak_mb", f"{RSS[os.path.join(out, 'lean.out')]:.0f}")
    txt = open(os.path.join(out, "lean.out")).read()
    proved = e == 0 and "error" not in txt and f"'{P}' depends on axioms" in txt
    if a.mock:
        proved = proved and "sorryAx" in txt
    put("status", "proved" if proved else "lean_fail")
    m_ = re.search(r"depends on axioms: \[(.*?)\]", txt, re.S)
    if m_:
        ax = [x.strip() for x in m_.group(1).split(",")]
        put("axioms_total", len(ax))
        put("axioms_native", sum(1 for x in ax if "native" in x))
        put("axioms_sorry", sum(1 for x in ax if "sorry" in x))
        put("axioms_other", ";".join(x for x in ax if "native" not in x))
    if a.emit_test and proved:
        emit_test(a.emit_test, n, N, P, pkg, cls, chunks, body, checks, qdefs, chk_line, rm,
                  leaves, res, lemma, thm, cls_body, Tl, T, path, Ls)
        put("emit_test", a.emit_test)
    put("end", time.strftime("%Y-%m-%d %H:%M:%S"))
    kv.close()


def emit_test(dirname, n, N, P, pkg, cls, chunks, body, checks, qdefs, chk_line, rm, leaves,
              res, lemma, thm, cls_body, Tl, T, path, Ls):
    """One self-contained test file (no module imports beyond the library) with the
    certificates copied to DIR/data/<prefix>_<key>.{pog,lrat}, relative paths."""
    name = f"Dedekind{N}Corner"
    pre = f"ded{N}c"
    dd = os.path.join(dirname, "data")
    os.makedirs(dd, exist_ok=True)

    def files(r, key):
        out = []
        for p in r["files"]:
            ext = os.path.splitext(p)[1]
            dst = f"{pre}_{key}{ext}"
            shutil.copy(p, os.path.join(dd, dst))
            out.append(f'"data/{dst}"')
        if r.get("keep"):
            dst = f"{pre}_{key}.keep"
            shutil.copy(r["keep"], os.path.join(dd, dst))
            out.append(f'(keep := "data/{dst}")')
        return " ".join(out)

    # a non-canonical orbit element, a wrong orbit size, a non-monotone mask
    i3 = next(i for i, (r, o) in enumerate(cls) if o > 1)
    r3, o3 = cls[i3]
    pm = point_maps(n)
    img = max(sum(((r3 >> int(y)) & 1) << int(pm[k][y]) for y in range(1 << n))
              for k in range(len(pm)))
    L = ["import CountCatcherMath.Command", "import CountCatcherMath.Families.DedekindCorner", "",
         f"/-! The Dedekind number M({N}) = {M[N]} by the {len(cls)} S_{n}-classes of the lower",
         f"    corner (`CountCatcherMath/Families/DedekindCorner.lean`), the shape of the M(8) run:",
         "    side data and side checks by `decide +kernel`, one `count_models` leaf per class",
         "    (`cube (Dedekind.cnf (n + 2)) (lits n r)`), split classes by a `SplitTree` of",
         "    sub-cubes, the assembly `card_eq_of_classes` with the certified M(n). Data from",
         f"    `scripts/showcase/dedekind_corner.py --n {n} --emit-test` (`data/{pre}_*`). -/", "",
         "open CountCatcher CountCatcher.DedekindCorner", "", "set_option maxRecDepth 100000", "",
         f"namespace {pkg}", "", *body, "", *checks, *qdefs, "",
         *(chk_line(k) for k in range(len(chunks))), "", f"end {pkg}", "",
         f"count_models {pkg}.dedekind{n} via (Dedekind.card_of_check (n := {n})) "
         f"{files(rm, 'm' + str(n))} (count := {rm['count']})", ""]
    for key, i, pl in leaves:
        r = res[key]
        hint = f" (count := {r['count']})" if r["count"] > 0 else ""
        L.append(f"count_models {thm(key)} via ({lemma(i, pl)}) {files(r, key)}{hint}")
    L.append("")
    for i in sorted(cls_body):
        L += cls_body[i] + [""]
    L += Tl
    L += ["", "/-! The side check rejects a wrong orbit size, an orbit element that is not the",
          "    smallest, and a non-monotone mask; the representatives must increase strictly. -/", "",
          f"example : repOk {n} {pkg}.T {pkg}.Ls {pkg}.P ({r3}, {o3 + 1}) = false := by decide +kernel",
          f"example : repOk {n} {pkg}.T {pkg}.Ls {pkg}.P ({img}, {o3}) = false := by decide +kernel",
          f"example : repOk {n} {pkg}.T {pkg}.Ls {pkg}.P (1, 1) = false := by decide +kernel",
          f"example : sortedB [{cls[1][0]}, {cls[0][0]}] = false := by decide", ""]
    with open(os.path.join(dirname, f"{name}.lean"), "w") as f:
        f.write("\n".join(L) + "\n")


if __name__ == "__main__":
    main()

"""Graphs for the independent-set family on irregular graphs (the t5 files of lean/test/data).

Writes, for one graph on vertices 0..k-1:
  NAME.cnf    DIMACS CNF in the clause order of the Lean encoder `IndepSet.cnf`
              (one clause -(u+1) -(v+1) per edge, lexicographic in (u, v) with u < v),
              header "p cnf k m" (k, not the largest variable, so isolated vertices count)
  NAME.edges  one "u v" line per edge, u < v, sorted (input for the Lean edge-list literal)

Graphs:
  hypercube N          Q_N on 2^N vertices, u ~ v iff u xor v is a power of two
  cubic N SEED         random 3-regular graph on N vertices (configuration model with
                       rejection, Python's random.Random(SEED))
  col FILE             DIMACS coloring graph ("e u v" lines, 1-based, duplicates merged)

Usage: uv run scripts/gen_t5.py OUTDIR NAME hypercube N
       uv run scripts/gen_t5.py OUTDIR NAME cubic N SEED
       uv run scripts/gen_t5.py OUTDIR NAME col FILE
"""

import os
import random
import sys


def hypercube(n):
    k = 1 << n
    return k, {(u, u ^ (1 << i)) for u in range(k) for i in range(n) if u < u ^ (1 << i)}


def cubic(n, seed):
    rng = random.Random(seed)
    while True:
        stubs = [v for v in range(n) for _ in range(3)]
        rng.shuffle(stubs)
        edges = set()
        ok = True
        for i in range(0, len(stubs), 2):
            u, v = sorted(stubs[i : i + 2])
            if u == v or (u, v) in edges:
                ok = False
                break
            edges.add((u, v))
        if ok:
            return n, edges


def col(path):
    k, edges = None, set()
    with open(path) as f:
        for line in f:
            t = line.split()
            if t and t[0] == "p":
                k = int(t[2])
            elif t and t[0] == "e":
                u, v = int(t[1]) - 1, int(t[2]) - 1
                if u != v:
                    edges.add((min(u, v), max(u, v)))
    return k, edges


def main():
    out, name, kind, *args = sys.argv[1:]
    if kind == "hypercube":
        k, edges = hypercube(int(args[0]))
    elif kind == "cubic":
        k, edges = cubic(int(args[0]), int(args[1]))
    elif kind == "col":
        k, edges = col(args[0])
    else:
        sys.exit(f"unknown graph kind {kind}")
    edges = sorted(edges)
    with open(os.path.join(out, name + ".cnf"), "w") as f:
        f.write(f"c independent sets of {name} ({kind} {' '.join(args)})\n")
        f.write(f"p cnf {k} {len(edges)}\n")
        for u, v in edges:
            f.write(f"-{u + 1} -{v + 1} 0\n")
    with open(os.path.join(out, name + ".edges"), "w") as f:
        for u, v in edges:
            f.write(f"{u} {v}\n")
    print(f"{name}: k={k} m={len(edges)}")


if __name__ == "__main__":
    main()

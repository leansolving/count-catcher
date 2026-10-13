"""DIMACS CNF for domino tilings of an R x C board (perfect matchings of the grid graph).

One variable per edge, numbered row-major over cells, horizontal edge before vertical edge.
Per vertex (row-major): one at-least-one clause over its incident edges, then pairwise
at-most-one clauses. No auxiliary variables, so #models = #tilings.

Usage: uv run scripts/gen_domino.py R [C]
"""

import sys
from itertools import combinations


def domino_cnf(rows, cols):
    var = {}
    for r in range(rows):
        for c in range(cols):
            for dr, dc in ((0, 1), (1, 0)):
                if r + dr < rows and c + dc < cols:
                    var[((r, c), (r + dr, c + dc))] = len(var) + 1
    inc = {(r, c): [] for r in range(rows) for c in range(cols)}
    for (a, b), v in var.items():
        inc[a].append(v)
        inc[b].append(v)
    clauses = []
    for vtx in sorted(inc):
        vs = sorted(inc[vtx])
        clauses.append(vs)
        clauses += [[-a, -b] for a, b in combinations(vs, 2)]
    return len(var), clauses


def main():
    rows = int(sys.argv[1])
    cols = int(sys.argv[2]) if len(sys.argv) > 2 else rows
    nvars, clauses = domino_cnf(rows, cols)
    out = [
        f"c domino tilings of the {rows} x {cols} board",
        f"p cnf {nvars} {len(clauses)}",
    ]
    out += [" ".join(map(str, cl)) + " 0" for cl in clauses]
    print("\n".join(out))


if __name__ == "__main__":
    main()

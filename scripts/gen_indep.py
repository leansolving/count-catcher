"""DIMACS CNF for independent sets of the R x C grid graph (hard squares).

Variable (r, c) is r*C + c + 1. One binary clause per edge, row-major over cells,
right edge before down edge. No auxiliary variables, so #models = #independent sets
(OEIS A006506 for square grids).

Usage: uv run scripts/gen_indep.py R [C]          print the CNF
       uv run scripts/gen_indep.py --count R [C]  print the count (row-mask transfer DP)
"""

import sys


def indep_cnf(rows, cols):
    v = lambda r, c: r * cols + c + 1
    clauses = []
    for r in range(rows):
        for c in range(cols):
            if c + 1 < cols:
                clauses.append([-v(r, c), -v(r, c + 1)])
            if r + 1 < rows:
                clauses.append([-v(r, c), -v(r + 1, c)])
    return rows * cols, clauses


def indep_count(rows, cols):
    if rows == 0 or cols == 0:
        return 1
    masks = [m for m in range(1 << cols) if m & (m >> 1) == 0]
    ways = {m: 1 for m in masks}
    for _ in range(rows - 1):
        ways = {m: sum(w for p, w in ways.items() if p & m == 0) for m in masks}
    return sum(ways.values())


def main():
    args = sys.argv[1:]
    count = args and args[0] == "--count"
    if count:
        args = args[1:]
    rows = int(args[0])
    cols = int(args[1]) if len(args) > 1 else rows
    if count:
        print(indep_count(rows, cols))
        return
    nvars, clauses = indep_cnf(rows, cols)
    out = [
        f"c independent sets of the {rows} x {cols} grid",
        f"p cnf {nvars} {len(clauses)}",
    ]
    out += [" ".join(map(str, cl)) + " 0" for cl in clauses]
    print("\n".join(out))


if __name__ == "__main__":
    main()

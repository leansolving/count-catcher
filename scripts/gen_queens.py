"""DIMACS CNF for the n-queens problem.

Variable (r, c) is r*n + c + 1. Clauses: per row an at-least-one clause and pairwise
at-most-one; pairwise at-most-one per column, per diagonal and per anti-diagonal.
No auxiliary variables, so #models = #solutions (OEIS A000170).

Usage: uv run scripts/gen_queens.py N
"""

import sys
from itertools import combinations


def queens_cnf(n):
    v = lambda r, c: r * n + c + 1
    clauses = []

    def amo(cells):
        clauses.extend([[-v(*a), -v(*b)] for a, b in combinations(cells, 2)])

    for r in range(n):
        row = [(r, c) for c in range(n)]
        clauses.append([v(*x) for x in row])
        amo(row)
    for c in range(n):
        amo([(r, c) for r in range(n)])
    for d in range(-(n - 1), n):
        amo([(r, r - d) for r in range(n) if 0 <= r - d < n])
    for s in range(2 * n - 1):
        amo([(r, s - r) for r in range(n) if 0 <= s - r < n])
    return n * n, clauses


def main():
    n = int(sys.argv[1])
    nvars, clauses = queens_cnf(n)
    out = [f"c {n}-queens", f"p cnf {nvars} {len(clauses)}"]
    out += [" ".join(map(str, cl)) + " 0" for cl in clauses]
    print("\n".join(out))


if __name__ == "__main__":
    main()

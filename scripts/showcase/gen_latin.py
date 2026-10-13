"""DIMACS CNF whose models are the Latin squares of order n (optionally reduced).

Variable x[r][c][s] = (r*n + c)*n + s + 1: cell (r, c) holds symbol s. Exactly one symbol
per cell, each symbol exactly once per row and per column (one at-least-one clause plus
pairwise at-most-one clauses each). With --reduced, unit clauses fix the first row and the
first column to the identity. No auxiliary variables: #models = #Latin squares (OEIS A002860,
reduced: A000315).

Usage: uv run scripts/showcase/gen_latin.py N [--reduced]
"""

import sys
from itertools import combinations

TOTAL = {1: 1, 2: 2, 3: 12, 4: 576, 5: 161280, 6: 812851200, 7: 61479419904000,
         8: 108776032459082956800, 9: 5524751496156892842531225600}
REDUCED = {1: 1, 2: 1, 3: 1, 4: 4, 5: 56, 6: 9408, 7: 16942080, 8: 535281401856,
           9: 377597570964258816}


def main():
    n = int(sys.argv[1])
    red = "--reduced" in sys.argv[2:]
    x = lambda r, c, s: (r * n + c) * n + s + 1
    cls = []

    def exactly_one(lits):
        cls.append(lits)
        cls.extend([-a, -b] for a, b in combinations(lits, 2))

    R = range(n)
    for r in R:
        for c in R:
            exactly_one([x(r, c, s) for s in R])
    for s in R:
        for r in R:
            exactly_one([x(r, c, s) for c in R])
        for c in R:
            exactly_one([x(r, c, s) for r in R])
    if red:
        cls.extend([x(0, c, c)] for c in R)
        cls.extend([x(r, 0, r)] for r in range(1, n))
    exp = (REDUCED if red else TOTAL).get(n, "unknown")
    out = [f"c Latin squares of order {n}{' (reduced)' if red else ''}", f"c expected {exp}",
           f"p cnf {n ** 3} {len(cls)}"]
    out += [" ".join(map(str, c)) + " 0" for c in cls]
    print("\n".join(out))


if __name__ == "__main__":
    main()

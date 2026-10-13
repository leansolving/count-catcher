"""DIMACS CNF whose models are the monotone Boolean functions on n variables.

Variable p+1 is the value of the function at point p of {0,1}^n (bit mask). For each covering
pair u < v (v = u plus one bit) the clause x_u -> x_v. The models are the up-sets of the
Boolean lattice, so #models = Dedekind number M(n) (OEIS A000372). No auxiliary variables.

Usage: uv run scripts/showcase/gen_dedekind.py N
"""

import sys

M = {0: 2, 1: 3, 2: 6, 3: 20, 4: 168, 5: 7581, 6: 7828354, 7: 2414682040998,
     8: 56130437228687557907788}


def main():
    n = int(sys.argv[1])
    cls = [[-(u + 1), (u | 1 << b) + 1] for u in range(1 << n) for b in range(n) if not u >> b & 1]
    out = [f"c Dedekind: monotone Boolean functions on {n} variables",
           f"c expected {M.get(n, 'unknown')}", f"p cnf {1 << n} {len(cls)}"]
    out += [" ".join(map(str, c)) + " 0" for c in cls]
    print("\n".join(out))


if __name__ == "__main__":
    main()

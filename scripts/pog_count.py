"""Exact model count of the POG declared in a CPOG file (no proof checking).

Support-local convention: S(u) is the set of original variables below u,
c(u) the number of satisfying assignments of S(u). Negation: 2^|S| - c. Product: disjoint
supports (checked), product of counts. Sum: lift both sides to the union support, add.
Final count: c(root) * 2^(V - |S(root)|), V from the CNF header.

Usage: uv run scripts/pog_count.py FORMULA.cnf CERT.cpog
"""

import sys


def num_vars(cnf_path):
    with open(cnf_path) as f:
        for line in f:
            if line.startswith("p cnf"):
                return int(line.split()[2])
    raise ValueError("no header")


def main():
    V = num_vars(sys.argv[1])
    supp, cnt = {}, {}
    root = None

    def lit(l):
        v = abs(l)
        if v <= V:
            s, c = frozenset([v]), 1
        else:
            s, c = supp[v], cnt[v]
        return (s, c) if l > 0 else (s, (1 << len(s)) - c)

    with open(sys.argv[2]) as f:
        for line in f:
            t = line.split()
            if not t or t[0] in ("c", "d"):
                continue
            if t[0] == "r":
                root = int(t[1])
            elif t[1] == "p":
                u, args = int(t[2]), [int(x) for x in t[3:-1]]
                s, c = frozenset(), 1
                for a in args:
                    sa, ca = lit(a)
                    if s & sa:
                        sys.exit(f"product {u}: overlapping supports")
                    s, c = s | sa, c * ca
                supp[u], cnt[u] = s, c
            elif t[1] == "s":
                u, a, b = int(t[2]), int(t[3]), int(t[4])
                (sa, ca), (sb, cb) = lit(a), lit(b)
                s = sa | sb
                supp[u] = s
                cnt[u] = (ca << (len(s) - len(sa))) + (cb << (len(s) - len(sb)))
    if root is None:
        sys.exit("no root declaration (r line)")
    s, c = lit(root)
    print(c << (V - len(s)))


if __name__ == "__main__":
    main()

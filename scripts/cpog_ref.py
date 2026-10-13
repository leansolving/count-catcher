"""Unverified reference checker for CPOG certificates (acceptance conditions C1-C8).

Purpose: a readable model of the semantics the Lean checker must implement, a harness for the
adversarial suite (each condition can be switched off to show that a malicious certificate is
rejected by exactly that condition), and a cost probe for the reverse direction by
evaluation. Not part of any trusted base.

Conventions: DIMACS numbering (variables and clause IDs start at 1). Counts are
support-local.

Usage:
  uv run scripts/cpog_ref.py FORMULA.cnf CERT.cpog [--reverse=delete|eval] [--off=C3,C4,...]
Conditions that can be switched off: C2 (fresh extension variables), C3 (product
disjointness), C4 (exclusion hints restricted to defining clauses), C5 (fresh clause IDs),
C6mask (mask the clause before checking its deletion), C6def (no deletion of defining
clauses), C7 (final state: only defining clauses and the root unit remain).
--norup skips all RUP checks (unsound; only for measuring the cost of the other parts).
"""

import sys
import time


class Reject(Exception):
    pass


def read_cnf(path):
    V, clauses = None, []
    cur = []
    with open(path) as f:
        for line in f:
            t = line.split()
            if not t or t[0] == "c":
                continue
            if t[0] == "p":
                V = int(t[2])
                continue
            for x in map(int, t):
                if x == 0:
                    clauses.append(tuple(cur))
                    cur = []
                else:
                    cur.append(x)
    return V, clauses


class Checker:
    def __init__(self, V, cnf, off=(), reverse="delete"):
        self.V, self.off, self.reverse = V, set(off), reverse
        self.db = {}  # id -> (lits, is_def)
        for i, c in enumerate(cnf, 1):
            if any(abs(l) > V for l in c):
                raise Reject(f"C1: input clause {i} leaves the universe")
            self.db[i] = (c, False)
        self.ninput = len(cnf)
        self.input_clauses = list(cnf)
        self.node = {}  # ext var -> ('p', args) | ('s', x, y)
        self.supp = {}
        self.cnt = {}
        self.last_var = V
        self.root = None
        self.stats = {"eval_node_visits": 0, "eval_clauses": 0}
        self.norup = False

    # --- helpers ---
    def defined(self, l):
        v = abs(l)
        return 1 <= v <= self.V or v in self.node

    def s(self, l):
        v = abs(l)
        return frozenset([v]) if v <= self.V else self.supp[v]

    def c(self, l):
        v = abs(l)
        base = 1 if v <= self.V else self.cnt[v]
        return base if l > 0 else (1 << len(self.s(l))) - base

    def add_clause(self, cid, lits, is_def):
        if cid in self.db and "C5" not in self.off:
            raise Reject(f"C5: clause ID {cid} already in use")
        self.db[cid] = (tuple(lits), is_def)

    def rup(self, lits, hints, only_defs=False):
        """Strict LRAT-style RUP: every hint must be unit or conflicting."""
        if self.norup:
            return
        val = {}
        for l in lits:
            val[abs(l)] = l < 0  # assign the negation of the clause
        for h in hints:
            if h not in self.db:
                raise Reject(f"hint {h} is not an active clause")
            hl, is_def = self.db[h]
            if only_defs and not is_def:
                raise Reject(f"C4: exclusion hint {h} is not a defining clause")
            unassigned = None
            satisfied = False
            for l in hl:
                v = abs(l)
                if v in val:
                    if val[v] == (l > 0):
                        satisfied = True
                        break
                elif unassigned is None or unassigned == l:
                    unassigned = l
                else:
                    raise Reject(f"hint {h} is not unit")
            if satisfied:
                raise Reject(f"hint {h} is satisfied")
            if unassigned is None:
                return  # conflict
            val[abs(unassigned)] = unassigned > 0
        raise Reject("RUP hints end without conflict")

    # --- steps ---
    def declare(self, cid, kind, u, args, hints):
        if "C2" not in self.off and not (u > self.V and u == self.last_var + 1):
            raise Reject(f"C2: extension variable {u} is not fresh")
        for a in args:
            if not self.defined(a) or abs(a) >= u and abs(a) > self.V:
                raise Reject(f"argument {a} of node {u} is undefined")
        if kind == "p":
            acc = frozenset()
            for a in args:
                sa = self.s(a)
                if acc & sa and "C3" not in self.off:
                    raise Reject(f"C3: product {u} has overlapping supports")
                acc |= sa
            count = 1
            for a in args:
                count *= self.c(a)
            defs = [[u] + [-a for a in args]] + [[-u, a] for a in args]
            self.node[u], self.supp[u], self.cnt[u] = ("p", args), acc, count
        else:
            x, y = args
            self.rup([-x, -y], hints, only_defs="C4" not in self.off)
            sx, sy = self.s(x), self.s(y)
            S = sx | sy
            count = (self.c(x) << (len(S) - len(sx))) + (
                self.c(y) << (len(S) - len(sy))
            )
            defs = [[-u, x, y], [u, -x], [u, -y]]
            self.node[u], self.supp[u], self.cnt[u] = ("s", x, y), S, count
        for k, d in enumerate(defs):
            self.add_clause(cid + k, d, True)
        self.last_var = u

    def add(self, cid, lits, hints):
        self.rup(lits, hints)
        self.add_clause(cid, lits, False)

    def delete(self, cid, hints):
        if cid not in self.db:
            raise Reject(f"deleting inactive clause {cid}")
        lits, is_def = self.db[cid]
        if is_def and "C6def" not in self.off:
            raise Reject(f"C6: deletion of defining clause {cid}")
        if "C6mask" not in self.off:
            del self.db[cid]
            self.rup(lits, hints)
        else:
            self.rup(lits, hints)
            del self.db[cid]

    # --- reverse by evaluation: conditioned support-local counts, cone-restricted ---
    def cond_count(self, rho, cache):
        """Count of the root under the partial assignment rho (var -> bool); nodes whose
        support misses dom(rho) keep their unconditioned count."""
        dom = frozenset(rho)

        def cl(l):
            v = abs(l)
            if v <= self.V:
                if v in rho:
                    base = 1 if rho[v] else 0
                else:
                    base = 1
                size = 0 if v in rho else 1
            else:
                base, size = cv(v)
            return (base if l > 0 else (1 << size) - base), size

        def cv(v):
            if v in cache:
                return cache[v]
            S = self.supp[v]
            if not (S & dom):
                r = (self.cnt[v], len(S))
            else:
                self.stats["eval_node_visits"] += 1
                size = len(S - dom)
                n = self.node[v]
                if n[0] == "p":
                    c = 1
                    for a in n[1]:
                        c *= cl(a)[0]
                else:
                    (cx, szx), (cy, szy) = cl(n[1]), cl(n[2])
                    c = (cx << (size - szx)) + (cy << (size - szy))
                r = (c, size)
            cache[v] = r
            return r

        return cl(self.root)[0]

    def finish(self):
        if self.root is None or (self.root,) not in (e[0] for e in self.db.values()):
            raise Reject("C7: root unit clause not derived")
        if self.reverse == "delete":
            if "C7" not in self.off:
                for cid, (lits, is_def) in self.db.items():
                    if not is_def and lits != (self.root,):
                        raise Reject(f"C7: clause {cid} {lits} remains at the end")
        else:
            for C in self.input_clauses:
                if any(-l in C for l in C):
                    continue  # tautological clause: implied by anything
                rho = {abs(l): l < 0 for l in C}
                self.stats["eval_clauses"] += 1
                if self.cond_count(rho, {}) != 0:
                    raise Reject(f"reverse by evaluation fails for input clause {C}")
        r = self.root
        return self.c(r) << (self.V - len(self.s(r)))


def run(cnf_path, cpog_path, off=(), reverse="delete", norup=False):
    V, cnf = read_cnf(cnf_path)
    ch = Checker(V, cnf, off, reverse)
    ch.norup = norup
    with open(cpog_path) as f:
        for lineno, line in enumerate(f, 1):
            t = line.split()
            if not t or t[0] == "c":
                continue
            try:
                if t[0] == "r":
                    ch.root = int(t[1])
                elif t[0] == "d":
                    if reverse == "delete":
                        ch.delete(int(t[1]), [int(x) for x in t[2:-1]])
                else:
                    cid, kind = int(t[0]), t[1]
                    nums = [int(x) for x in t[2:]]
                    if kind == "a":
                        z = nums.index(0)
                        ch.add(cid, nums[:z], nums[z + 1 : -1])
                    elif kind == "p":
                        ch.declare(cid, "p", nums[0], nums[1:-1], [])
                    elif kind == "s":
                        ch.declare(cid, "s", nums[0], nums[1:3], nums[3:-1])
            except Reject as e:
                raise Reject(f"line {lineno}: {e}")
            except (ValueError, KeyError, IndexError) as e:
                raise Reject(f"line {lineno}: malformed step ({type(e).__name__}: {e})")
    t_fin = time.time()
    count = ch.finish()
    ch.stats["finish_s"] = round(time.time() - t_fin, 2)
    return count, ch.stats


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    opts = dict(
        (a[2:].split("=", 1) + [""])[:2] for a in sys.argv[1:] if a.startswith("--")
    )
    off = [x for x in opts.get("off", "").split(",") if x]
    t0 = time.time()
    try:
        count, stats = run(
            args[0], args[1], off, opts.get("reverse", "delete"), "norup" in opts
        )
        print(f"ACCEPT count={count} time={time.time() - t0:.2f}s {stats}")
    except Reject as e:
        print(f"REJECT {e}")


if __name__ == "__main__":
    main()

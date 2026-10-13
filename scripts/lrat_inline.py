"""Untrusted post-processing of the part B refutation: inline single-use additions. The test
reference for `cpog2lrat --inline` (in memory, for small certificates; tools-src/cpog2lrat/
difftest.sh), which applies the same rule in one streaming pass.

Reads OUT.cnf and the trimmed text LRAT that scripts/lrat_trim.py (or `cpog2lrat --trim`, with
--keep if wanted) writes without --delete and --binary: initial clauses 1..K are the clauses of
OUT.cnf, additions K+1..N follow in order, the last step is the empty clause [root unit, negated
root]. Writes DST with the same initial clauses (OUT.cnf and the keep mask stay valid; a kept
initial clause that no step cites any more is harmless), the surviving additions renumbered by
position after them with their literals as read, with --delete every clause deleted after its
last use (as lrat_trim.py), with --binary in binary LRAT. Prints one statistics line, the one
`cpog2lrat --inline` writes to stderr (without its fifo_peak field).

The checker's rule (Lean core v4.30.0, Std/Tactic/BVDecide/LRAT/Internal/Formula/
Implementation.lean performRupAdd 219-238, confirmRupHint 176-195; Clause.lean reduce 208-258):
the negated clause is assigned; then hint by hint, in order, a literal counts as false iff its
negation is assigned; no non-false literal: conflict, the step is accepted and the remaining
hints are not looked at; exactly one non-false literal u (repeated literals count once): u is
assigned (if u is already true the hint changes nothing and is accepted); two or more: the step
fails; a missing or deleted hint fails; the hints run out without a conflict: the step fails.
Lean also keeps the unit clauses of the formula assigned between steps; the replay here leaves
them out (the rule of drat-trim's lrat-check), which only makes fewer steps succeed (more
assigned literals never turn an accepted step into a failing one), so every output accepted
here is accepted by Lean and by lrat-check.

The rule (window W, default 4096, one forward pass). Static data from the input lists (the
final step not counted): an addition is single if exactly one step cites it (once); it is
far-cited if some step cites it from more than W positions later. A clause is at hand for the
step E being read if it is an initial clause, the root unit, an addition at most W positions
before E, or far-cited (a streaming pass keeps the last W additions and the literals of the
far-cited ones and the root unit).
Each step E is replayed: from the negation of E, hint by hint in order. A hint after the
conflict, and a hint whose unit is already true, is dropped. A hint D is a candidate if D is a
single addition, not the root unit, at most W positions before E, its own replay succeeded, and
every element of D's current hint list is at hand: D's list is replayed in E's state at the
citation; if D reduces there to the unit x, D's hints run until one of them yields x (cut: D's
remaining hints are dropped, E's own hints follow) or a conflict (E is done); a hint that is
non-unit there rejects the candidate (D stays cited); hints of D whose unit is already true are
dropped. If D reduces to a conflict, D's hints must reach one too. A repeated hint is dropped as
an already-true unit. If E's own replay fails (a non-unit hint, no conflict at the end), E keeps
its list unchanged and is never a candidate. Otherwise, at the end of E: E gets the new list,
the inlined steps are removed, and each dropped hint that is a single addition (not the root
unit) has lost its only citation: it is removed if it lies at most W positions before E (its
own hints then lose a citation in turn), else it stays (a streaming pass has written it).
Forward order, so a chain of single-use units collapses into its last consumer.

Usage: uv run scripts/lrat_inline.py OUT.cnf IN.lrat DST [--delete] [--binary] [--window W]
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lrat_trim import dimacs_clauses, taut, varint  # noqa: E402


class Fail(Exception):
    pass


def read_lrat(path, first):
    lits, hints = [], []
    with open(path) as f:
        for k, line in enumerate(f):
            t = [int(x) for x in line.split()]
            z = t.index(0, 1)
            if t[0] != first + k:
                raise Fail(f"addition IDs not consecutive at line {k + 1}")
            if taut(t[1:z]):
                raise Fail(f"tautological addition {t[0]}")
            lits.append(t[1:z])
            hints.append(t[z + 1 : -1])
    return lits, hints


def main():
    args = sys.argv[1:]
    flags, pos, k = {}, [], 0
    while k < len(args):
        a = args[k]
        if a == "--window":
            flags[a], k = args[k + 1], k + 2
        elif a.startswith("--"):
            flags[a], k = True, k + 1
        else:
            pos.append(a)
            k += 1
    cnf, src, dst = pos
    W = int(flags.get("--window", 4096))

    init = dimacs_clauses(cnf)
    if any(taut(c) for c in init):
        raise Fail("OUT.cnf has a tautology")
    K = len(init)
    alits, hints = read_lrat(src, K + 1)
    N = K + len(alits)
    C = [()] + init + alits  # C[id] = literals as read
    H = [None] * (K + 1) + hints  # H[id] = hint list of an addition, None if removed/initial
    fin = N
    if C[fin] or len(H[fin]) != 2:
        raise Fail("the last step is not the final empty clause")
    root = H[fin][0]
    protected = {fin, root}

    uses = [0] * (N + 1)
    far = bytearray(N + 1)
    for i in range(K + 1, fin):
        for h in H[i]:
            uses[h] += 1
            if h > K and i - h > W:
                far[h] = 1
    bad = bytearray(N + 1)
    nv = max((abs(l) for c in C for l in c), default=0)
    off = nv
    T = [0] * (2 * nv + 1)
    st = 0
    s = {"inlined": 0, "rejected": 0, "not_at_hand": 0, "invalid": 0, "dead_removed": 0,
         "dead_written": 0}

    def at_hand(g, E):
        return g <= K or g == root or E - g <= W or far[g]

    def reduce(c):
        """(False, _) if two different literals are not false, else (True, unit or 0)."""
        u = 0
        for l in c:
            if T[off - l] == st:
                continue
            if u == 0:
                u = l
            elif u != l:
                return False, 0
        return True, u

    def dec(g, E):
        """g lost a citation: a single addition is dead (removed within the window)."""
        stack = [g]
        while stack:
            g = stack.pop()
            if g <= K or g in protected or uses[g] != 1:
                continue
            if E - g > W:
                s["dead_written"] += 1
                continue
            s["dead_removed"] += 1
            stack.extend(H[g])
            H[g] = None

    for E in range(K + 1, N + 1):
        HE = H[E]
        if HE is None:
            continue
        st += 1
        for l in C[E]:
            T[off - l] = st
        new, inl, drops = [], [], []
        done, ok = False, True
        for h in HE:
            if done:
                drops.append(h)
                continue
            if h > K and H[h] is None:
                raise Fail(f"step {E} cites removed clause {h}")
            ok, u = reduce(C[h])
            if not ok:
                break
            if u and T[off + u] == st:
                drops.append(h)
                continue
            if h > K and uses[h] == 1 and h not in protected and not bad[h] and E - h <= W:
                G = H[h]
                if all(at_hand(g, E) for g in G):
                    trail, kept, gdrops, stage = [], [], [], "run"
                    for g in G:
                        if stage != "run":  # after the cut or the conflict
                            gdrops.append(g)
                            continue
                        okg, v = reduce(C[g])
                        if not okg:
                            stage = "bad"
                            break
                        if v == 0:
                            stage = "conflict"
                            kept.append(g)
                        elif T[off + v] == st:
                            gdrops.append(g)
                        else:
                            T[off + v] = st
                            trail.append(v)
                            kept.append(g)
                            if v == u:
                                stage = "cut"
                    if stage in ("cut", "conflict"):
                        inl.append(h)
                        new.extend(kept)
                        drops.extend(gdrops)
                        done = stage == "conflict"
                        continue
                    for v in trail:
                        T[off + v] = 0
                    s["rejected"] += 1
                else:
                    s["not_at_hand"] += 1
            new.append(h)
            if u == 0:
                done = True
            else:
                T[off + u] = st
        if not ok or not done:
            # E's own list does not pass: unchanged, never a candidate (its inlines undone)
            bad[E] = 1
            s["invalid"] += 1
            continue
        H[E] = new
        s["inlined"] += len(inl)
        for h in inl:
            H[h] = None
        for g in drops:
            dec(g, E)

    # renumber and write
    keep_ids = [i for i in range(K + 1, N + 1) if H[i] is not None]
    new_id = {c: c for c in range(1, K + 1)}
    for k2, i in enumerate(keep_ids):
        new_id[i] = K + 1 + k2
    steps = [(new_id[i], C[i], [new_id[h] for h in H[i]]) for i in keep_ids]
    fin2 = steps[-1][0]
    last = {}
    for i, _, hs in steps:
        for h in hs:
            last[h] = i
    dels = {}
    if "--delete" in flags:
        for c in range(1, fin2):
            d = last.get(c, max(c, K + 1))
            if d < fin2:
                dels.setdefault(d, []).append(c)
    if "--binary" in flags:
        buf = bytearray()
        for i, ls, hs in steps:
            buf.append(ord("a"))
            for x in [i, *ls]:
                varint(x, buf)
            buf.append(0)
            for x in hs:
                varint(x, buf)
            buf.append(0)
            if i in dels:
                buf.append(ord("d"))
                for x in dels[i]:
                    varint(x, buf)
                buf.append(0)
        with open(dst, "wb") as f:
            f.write(buf)
    else:
        with open(dst, "w") as f:
            for i, ls, hs in steps:
                f.write(" ".join(map(str, [i, *ls, 0, *hs, 0])) + "\n")
                if i in dels:
                    f.write(f"{i} d {' '.join(map(str, dels[i]))} 0\n")
    adds_in = N - 1 - K
    hints_in = sum(len(hints[i]) for i in range(adds_in))
    hints_out = sum(len(hs) for _, _, hs in steps[:-1])
    fc = [i for i in range(K + 1, fin) if far[i]]
    print(f"inline window={W} additions_in={adds_in} additions_out={len(steps) - 1} "
          f"hints_in={hints_in} hints_out={hints_out} "
          + " ".join(f"{a}={b}" for a, b in s.items())
          + f" far_cited={len(fc)} far_lits={sum(len(C[i]) for i in fc)}")
    if "--delete" in flags:
        print(f"deleted={sum(map(len, dels.values()))}")


if __name__ == "__main__":
    try:
        main()
    except Fail as e:
        sys.exit(f"lrat_inline: {e}")

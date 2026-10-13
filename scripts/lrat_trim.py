"""Backward trimming of the part B refutation: the test reference for `cpog2lrat --trim` and
`cpog2lrat --keep`.

Reads IN.lrat as scripts/cpog2lrat.py writes it without options (text, no deletions, the last
step the empty clause from the root unit and the negated root) and writes DST as the native
`cpog2lrat --trim` does with the same options: only the additions in the backward cone of the
last step, renumbered by position after the initial clauses (the IDs up to the negated root do
not change); with --delete every clause deleted after the last kept step that cites it (a clause
never cited: after its own step, an initial clause after the first step; the root unit and the
negated root stay); with --binary in binary LRAT. In memory, for small certificates
(tools-src/cpog2lrat/difftest.sh). Prints the native statistics line ("trim ...", which the
native translator writes to stderr) on stdout, with --keep then the "keep ..." line, with
--delete then "deleted=K" (the native stdout field); FORMULA.cnf gives the input clauses.

--keep (as `cpog2lrat --keep`) keeps only the initial clauses that the kept steps cite, numbers
them by position among themselves, and writes two more files next to DST (same stem): .keep, the
mask over all initial clauses of part B (the clauses of FORMULA.cnf, tautologies included, the
defining clauses of the POG file IN.pog in node order, the negated root; '1' kept, '0' not,
no newline), and .cnf, the kept clauses of IN.cnf (the Python translator's OUT.cnf).

Usage: uv run scripts/lrat_trim.py FORMULA.cnf IN.lrat DST [--delete] [--binary] [--keep]
"""

import os
import sys


def taut(c):
    s = set(c)
    return any(-x in s for x in s)


def dimacs_clauses(path):
    """The clauses of a DIMACS file, in order."""
    out, cur = [], []
    with open(path) as f:
        for line in f:
            t = line.split()
            if not t or t[0] in ("c", "p"):
                continue
            for x in map(int, t):
                if x:
                    cur.append(x)
                else:
                    out.append(cur)
                    cur = []
    return out


def pog_defs(path):
    """The defining clauses of a POG file (translator output) in node order, then [-root]."""
    out = []
    with open(path) as f:
        lines = f.read().split("\n")
    v, root = int(lines[0].split()[1]), int(lines[1].split()[1])
    for i, line in enumerate(l for l in lines[2:] if l):
        t = line.split()
        u = v + 1 + i
        if t[0] == "p":
            args = [int(x) for x in t[1:-1]]
            out += [[u] + [-a for a in args]] + [[-u, a] for a in args]
        else:
            x, y = int(t[1]), int(t[2])
            out += [[-u, x, y], [u, -x], [u, -y]]
    return out + [[-root]]


def varint(x, buf):
    u = 2 * x if x >= 0 else -2 * x + 1
    while u >= 128:
        buf.append((u & 127) | 128)
        u >>= 7
    buf.append(u)


def main():
    flags = [a for a in sys.argv[1:] if a.startswith("--")]
    cnf, src, dst = [a for a in sys.argv[1:] if not a.startswith("--")]
    keep = "--keep" in flags
    steps = []  # (id, lits, hints)
    with open(src) as f:
        for line in f:
            t = [int(x) for x in line.split()]
            z = t.index(0, 1)
            steps.append((t[0], t[1:z], t[z + 1 : -1]))
    fin, lits, hints = steps[-1]
    assert not lits and len(hints) == 2, "the last step is not the final empty clause"
    neg_root = hints[1]
    first = neg_root + 1
    at = {s[0]: s for s in steps}
    cone, todo = {fin}, [fin]
    while todo:
        for h in at[todo.pop()][2]:
            if h >= first and h not in cone:
                cone.add(h)
                todo.append(h)
    kept = [s for s in steps if s[0] in cone]
    cited = sorted({h for _, _, hs in kept for h in hs if h < first})
    # --keep: a cited initial clause gets its rank, the additions follow the cited ones
    new = {c: k + 1 for k, c in enumerate(cited)} if keep else {}
    base = len(cited) if keep else neg_root
    new.update({s[0]: base + 1 + k for k, s in enumerate(kept)})
    kept = [(new[i], ls, [new.get(h, h) for h in hs]) for i, ls, hs in kept]
    fin = kept[-1][0]
    last = {}
    for i, _, hs in kept:
        for h in hs:
            last[h] = i
    dels = {}
    if "--delete" in flags:
        for c in range(1, fin):
            d = last.get(c, max(c, base + 1))
            if d < fin:
                dels.setdefault(d, []).append(c)
    if "--binary" in flags:
        buf = bytearray()
        for i, ls, hs in kept:
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
            for i, ls, hs in kept:
                f.write(" ".join(map(str, [i, *ls, 0, *hs, 0])) + "\n")
                if i in dels:
                    f.write(f"{i} d {' '.join(map(str, dels[i]))} 0\n")
    inputs = dimacs_clauses(cnf)
    mk = sum(not taut(c) for c in inputs)
    ci = sum(1 for h in cited if h <= mk)
    cn = int(neg_root in cited)
    print(f"trim additions_kept={len(kept) - 1} additions_total={len(steps) - 1} "
          f"cited_input={ci} input_clauses={mk} cited_defs={len(cited) - ci - cn} "
          f"def_clauses={neg_root - 1 - mk} cited_neg_root={cn}")
    if keep:
        stem = os.path.splitext(dst)[0]
        initial = inputs + pog_defs(src[:-5] + ".pog")
        ids = [c for c in initial if not taut(c)]
        assert len(ids) == neg_root, "the POG file does not match the LRAT numbering"
        cs, v, mask = set(cited), 0, []
        for c in initial:
            if taut(c):
                mask.append("0")
            else:
                v += 1
                mask.append("1" if v in cs else "0")
        with open(stem + ".keep", "w") as f:
            f.write("".join(mask))
        with open(src[:-5] + ".cnf") as f:
            head, *body = f.read().split("\n")[:-1]
        with open(stem + ".cnf", "w") as f:
            f.write(f"{' '.join(head.split()[:3])} {len(cited)}\n")
            f.writelines(body[c - 1] + "\n" for c in cited)
        print(f"keep keep_ones={len(cited)} keep_len={len(mask)}")
    if "--delete" in flags:
        print(f"deleted={sum(map(len, dels.values()))}")


if __name__ == "__main__":
    main()

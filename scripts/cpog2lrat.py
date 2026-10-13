"""Translate the forward part of a CPOG certificate into an LRAT refutation.

With the reverse direction checked by evaluation, the forward direction F ∧ defs ⊨ r is the
unsatisfiability of F ∧ defs ∧ ¬r. This script writes
  OUT.cnf   F, then the defining clauses in declaration order (CPOG Table 2), then ¬r
  OUT.lrat  the CPOG additions renumbered, then the empty clause from the root unit and ¬r
  OUT.pog   the node table for part A: header "V <V>", root "r <lit>",
            one line per node in order, node i defining variable V+1+i (DIMACS):
            "p <args> 0" or "s <x> <y> <hints> 0" with each exclusion hint written as
            "<node>:<k>" (defining clause k of an earlier node, 0-based)
so that any verified LRAT checker (lrat-catcher, Std.Tactic.BVDecide.LRAT) can check it.
The POG format cannot express a non-fresh extension variable (C2) or an exclusion hint that
cites an input or derived clause (C4); such certificates are rejected here.
CPOG deletions are dropped (all of them come after the root unit); sum-node exclusion hints
belong to the POG check, not to this refutation. Untrusted: a wrong translation is rejected.

Two streaming passes over the certificate (declarations, then additions) with ID maps in
arrays, so multi-GB certificates need memory for about 16 bytes per clause ID only.

With --delete, a third pass inserts the deletion of every clause after its last use, which
bounds the live clause database of the LRAT checker (part B memory).

With --binary, OUT.lrat is written in binary LRAT (lrat-catcher detects the format from the
first byte).

Clause IDs follow the LRAT checker in Lean core (Std.Tactic.BVDecide.LRAT, v4.30), which
lrat-catcher runs unchanged: it stores clauses by position and ignores the IDs of additions.
`CNF.convertLRAT'` drops every tautological clause (one containing a literal and its
negation; `DefaultClause.ofArray` returns none) from the initial formula F ++ defs ++ [-r],
and `intActionToDefaultClauseAction` skips every tautological addition; repeated literals
are merged, not dropped. So a clause's ID here is its position among the non-tautological
clauses: tautological clauses are left out of OUT.cnf and OUT.lrat, hints citing them are
dropped (a tautology is never unit), and the later IDs move down. Without tautologies the
IDs are the DIMACS clause numbers, as before. The statistics line then ends with
"taut_dropped=K".

Usage: uv run scripts/cpog2lrat.py FORMULA.cnf CERT.cpog OUT [--delete] [--binary]
"""

import os
import sys
from array import array


def taut(c):
    """A clause containing a literal and its negation."""
    s = set(c)
    return any(-x in s for x in s)


ABSENT = -1  # ID map value of a tautological clause (no position in the checker)


def ids():
    """Growable map from clause IDs to integers (0 = unset), 8 bytes per ID."""
    return array("q")


def put(a, i, v):
    if i >= len(a):
        a.frombytes(bytes(8 * (i + 1 - len(a) + (1 << 20))))
    a[i] = v


def get(a, i):
    return a[i] if 0 < i < len(a) else 0


def varint(x, buf):
    """Binary LRAT number: 2|x| + (x < 0) in 7-bit groups, low group first."""
    u = 2 * x if x >= 0 else -2 * x + 1
    while u >= 128:
        buf.append((u & 127) | 128)
        u >>= 7
    buf.append(u)


def to_binary(src, dst):
    """Rewrite a text LRAT file in binary LRAT (drat-trim/lrat-trim format): addition
    'a' id lits 0 hints 0, deletion 'd' ids 0. Replaces dst (src may equal dst)."""
    tmp = dst + ".bin"
    with open(src) as fi, open(tmp, "wb") as fo:
        buf = bytearray()
        for line in fi:
            t = line.split()
            if len(t) > 1 and t[1] == "d":
                buf.append(100)  # 'd'
                for x in t[2:-1]:
                    varint(int(x), buf)
                buf.append(0)
            else:
                nums = [int(x) for x in t]
                z = nums.index(0, 1)
                buf.append(97)  # 'a'
                for x in nums[:z]:
                    varint(x, buf)
                buf.append(0)
                for x in nums[z + 1 : -1]:
                    varint(x, buf)
                buf.append(0)
            if len(buf) > 1 << 20:
                fo.write(buf)
                buf.clear()
        fo.write(buf)
    os.replace(tmp, dst)
    if src != dst:
        os.remove(src)


def add_deletions(out, last, first, final, root_unit, neg_root):
    """Pass 3 (--delete): copy OUT.lrat.tmp to OUT.lrat, deleting every clause after the last
    step that cites it (a clause never cited: after its own step, or after the first step for
    input and defining clauses). The root unit and the negated root stay until the final
    step. Deletions only shrink the clause database, so the refutation stays valid."""
    put(last, root_unit, final)
    put(last, neg_root, final)
    n = final - first  # steps first .. final-1 can be followed by deletions
    start = array("q", bytes(8 * (n + 1)))

    def step(c):
        s = get(last, c)
        return s if s else max(c, first)

    for c in range(1, final):
        d = step(c)
        if d < final:
            start[d - first] += 1
    acc = 0
    for i in range(n + 1):
        start[i], acc = acc, acc + start[i]
    order = array("q", bytes(8 * acc))
    fill = array("q", start)
    for c in range(1, final):
        d = step(c)
        if d < final:
            order[fill[d - first]] = c
            fill[d - first] += 1
    del fill
    with open(out + ".lrat.tmp") as fi, open(out + ".lrat", "w") as fo:
        for line in fi:
            fo.write(line)
            t = int(line.split(maxsplit=1)[0])
            if t < final:
                a, b = start[t - first], start[t - first + 1]
                if b > a:
                    fo.write(f"{t} d {' '.join(map(str, order[a:b]))} 0\n")
    os.remove(out + ".lrat.tmp")
    return acc


def main():
    args = [a for a in sys.argv[1:] if a not in ("--delete", "--binary")]
    delete = "--delete" in sys.argv[1:]
    binary = "--binary" in sys.argv[1:]
    cnf_path, cpog_path, out = args[:3]
    if os.path.abspath(out + ".cnf") == os.path.abspath(cnf_path):
        sys.exit(f"OUT.cnf would overwrite the input formula {cnf_path}; choose another OUT")
    V, m, cur = None, 0, []
    tin = []  # IDs of the tautological input clauses
    with open(cnf_path) as f:
        for line in f:
            t = line.split()
            if not t or t[0] == "c":
                continue
            if t[0] == "p":
                V = int(t[2])
                continue
            for x in map(int, t):
                if x == 0:
                    m += 1
                    if taut(cur):
                        tin.append(m)
                    cur = []
                else:
                    cur.append(x)
    mk = m - len(tin)  # input clauses with a position
    # Pass 1: declarations. New IDs of the defining clauses, POG file, C2 and C4.
    new = ids()  # old clause ID -> new ID
    node_of = ids()  # defining clause ID -> node index + 1
    decl_cid = []  # node -> ID of its first defining clause
    root, maxvar, ndefs, nkept = None, V, 0, 0  # nkept: defining clauses with a position
    empty_prod = {}  # variable of an empty product -> ID of its defining clause [u]
    with open(cpog_path) as f, open(out + ".pog", "w") as fp:
        fp.write(f"V {V}\n")
        for line in f:
            t = line.split()
            if not t or t[0] in ("c", "d"):
                continue
            if t[0] == "r":
                root = int(t[1])
                continue
            kind = t[1]
            if kind == "a":
                continue
            cid, nums = int(t[0]), [int(x) for x in t[2:]]
            node = len(decl_cid)
            if kind in ("p", "s") and nums[0] != V + 1 + node:
                sys.exit(f"C2: extension variable {nums[0]} is not V+1+{node}")
            if kind == "p":
                u, args = nums[0], nums[1:-1]
                ncls = len(args) + 1
                cls = [[u] + [-a for a in args]] + [[-u, a] for a in args]
                pl = "p " + " ".join(map(str, args)) + " 0"
                if not args:
                    empty_prod[u] = cid
            elif kind == "s":
                u, x, y = nums[0], nums[1], nums[2]
                ncls = 3
                cls = [[-u, x, y], [u, -x], [u, -y]]
                refs = []
                for h in nums[3:-1]:
                    nh = get(node_of, h)
                    if nh == 0:
                        sys.exit(
                            f"C4: exclusion hint {h} of node {u} is not a defining clause"
                        )
                    refs.append(f"{nh - 1}:{h - decl_cid[nh - 1]}")
                pl = f"s {x} {y} " + " ".join(refs) + " 0"
            else:
                sys.exit(f"unsupported step kind {kind!r} in step {cid}")
            fp.write(pl + "\n")
            maxvar = max(maxvar, u)
            for k in range(ncls):
                if taut(cls[k]):
                    put(new, cid + k, ABSENT)
                else:
                    nkept += 1
                    put(new, cid + k, mk + nkept)
                put(node_of, cid + k, node + 1)
            ndefs += ncls
            decl_cid.append(cid)
    del node_of
    if root is None:
        sys.exit("no root declaration (r line)")
    fp_root = f"r {root}\n"
    # The root line goes second; rewrite the small POG file.
    with open(out + ".pog") as fp:
        body = fp.read()
    head, rest = body.split("\n", 1)
    with open(out + ".pog", "w") as fp:
        fp.write(head + "\n" + fp_root + rest)
    tset, k = set(tin), 0
    for i in range(1, m + 1):
        if i in tset:
            put(new, i, ABSENT)
            k += 1
        else:
            put(new, i, i - k)
    neg_root = mk + nkept + 1
    ndrop = len(tin) + ndefs - nkept  # tautological clauses left out
    # Pass 2: defining clauses into OUT.cnf, additions renumbered into OUT.lrat.
    nxt, root_unit, nadds = neg_root + 1, None, 0
    last = ids()  # with --delete: new clause ID -> last step citing it
    lrat_path = out + (".lrat.tmp" if delete or binary else ".lrat")
    with open(cpog_path) as f, open(out + ".cnf", "w") as fc, open(lrat_path, "w") as fl:
        fc.write(f"p cnf {maxvar} {neg_root}\n")
        with open(cnf_path) as fi:
            cur = []
            for line in fi:
                t = line.split()
                if not t or t[0] in ("c", "p"):
                    continue
                for x in map(int, t):
                    if x == 0:
                        if not taut(cur):
                            fc.write(" ".join(map(str, cur + [0])) + "\n")
                        cur = []
                    else:
                        cur.append(x)
        for line in f:
            t = line.split()
            if not t or t[0] in ("c", "d", "r"):
                continue
            kind = t[1]
            if kind == "p":
                u, args = int(t[2]), [int(x) for x in t[3:-1]]
                cls = [[u] + [-a for a in args]] + [[-u, a] for a in args]
            elif kind == "s":
                u, x, y = int(t[2]), int(t[3]), int(t[4])
                cls = [[-u, x, y], [u, -x], [u, -y]]
            else:
                old, nums = int(t[0]), [int(x) for x in t[2:]]
                z = nums.index(0)
                lits, hints = nums[:z], nums[z + 1 : -1]
                nh = [get(new, h) for h in hints]
                if 0 in nh:
                    unknown = [h for h, v in zip(hints, nh) if v == 0]
                    sys.exit(
                        f"step {old}: hint(s) {unknown} cite no earlier input, defining or added clause"
                    )
                if taut(lits):  # skipped by the checker: no position
                    put(new, old, ABSENT)
                    ndrop += 1
                    continue
                nh = [v for v in nh if v != ABSENT]
                put(new, old, nxt)
                if delete:
                    for v in nh:
                        put(last, v, nxt)
                fl.write(" ".join(map(str, [nxt, *lits, 0, *nh, 0])) + "\n")
                if lits == [root]:
                    root_unit = nxt
                nxt += 1
                nadds += 1
                continue
            for c in cls:
                if not taut(c):
                    fc.write(" ".join(map(str, c)) + " 0\n")
        fc.write(f"{-root} 0\n")
        if root_unit is None and root in empty_prod:
            # constant true (valid formula): cpog-gen uses the defining clause [u] as the
            # root unit and derives no addition for it
            root_unit = get(new, empty_prod[root])
        if root_unit is None:
            sys.exit("no root unit clause among the additions")
        fl.write(f"{nxt} 0 {root_unit} {neg_root} 0\n")
    ndel = add_deletions(out, last, neg_root + 1, nxt, root_unit, neg_root) if delete else 0
    if binary:
        to_binary(out + (".lrat" if delete else ".lrat.tmp"), out + ".lrat")
    print(
        f"vars={maxvar} clauses={neg_root} (input {m}, defs {ndefs}) additions={nadds}"
        + (f" deleted={ndel}" if delete else "")
        + (f" taut_dropped={ndrop}" if ndrop else "")
    )


if __name__ == "__main__":
    main()

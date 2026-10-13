"""Graphs on n vertices up to isomorphism, by Burnside's lemma over Perm (Fin n) grouped by cycle
type, from certified model counts (CountCatcherMath/Families/GraphIso.lean, CountCatcherMath/CycleType.lean).

For every cycle type l of Perm (Fin n) (partitions of n; parts >= 2 in decreasing order, the
identity is []), the fixed-point formula symCnf F V (edgePerm n (rep n l)) is exported from the
Lean term (#export_cnf via the family lemma, so clause IDs match the theorem), counted by D4 and
certified:
  count > 0   cpog-gen-fwd -F -T 500 -G (forward half only), then the native cpog2lrat --delete
              --trim (text LRAT: the theorem file lets count_models choose embedding by size); a
              file larger than --embed-max, which count_models streams, is translated again
              with --keep --binary and passed with its keep file (part B on the cited clauses)
  count = 0   CaDiCaL LRAT refutation (tautological clauses left out)
The identity term uses the plain encoder F (the labelled count); with --split it is split by the
neighbourhood of vertex 0 into n formulas nbrCnf F n k (N(0) = {1, ..., k}), combined by
Fam.card_eq_of_split (sum of C(n-1, k) times the counts, `decide`). The theorem file has one
count_models per cycle type (with D4's count as hint), the Burnside assembly
(Fam.card_orbits_eq, class sizes and completeness checked by `decide`) and the
isomorphism-class form, then #print axioms. Lean runs with the precompiled checker as plugin.

Families (--family):
  clique:S      {G : SimpleGraph (Fin n) // G.CliqueFree S}                (CliqueFreeFam)
  ramsey:S:T    {G : SimpleGraph (Fin n) // G.CliqueFree S ∧ Gᶜ.CliqueFree T}  (RamseyFam)

Usage:
  uv run scripts/graph_orbits.py --family clique:3 --n 7 [--work DIR] [--out DIR] [-j K]
      [--lean LEANDIR] [--tools TOOLSDIR] [--split] [--witness TERM] [--inline] [--keep] [--no-lean]
      [--only-export]
Results: OUT/summary.tsv (one row per cycle type), OUT/T.lean (theorem file), OUT/lean.out,
OUT/result.txt (key=value). Certificates live in WORK (default OUT/work), deleted after a proof
unless --keep. The checked theorem file is WORK/T.lean; its certificate paths are relative to WORK
(e.g. "8_2/fwd.pog"), so OUT/T.lean is a copy for the record.
"""

import argparse
import concurrent.futures as cf
import filecmp
import math
import os
import platform
import re
import shutil
import subprocess
import sys
import time
from collections import Counter

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXT = "dylib" if platform.system() == "Darwin" else "so"
GEN_BIN, GEN_FL = "cpog-gen-fwd", ["-F", "-T", "500", "-G"]  # the generator and its options


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield []
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield [k] + rest


def cycle_types(n):
    """Cycle types of Perm (Fin n): parts >= 2, decreasing; the identity is []."""
    return [[k for k in p if k >= 2] for p in partitions(n)]


def class_size(n, l):
    c = Counter(l)
    z = (math.factorial(n - sum(l)) * math.prod(l)
         * math.prod(math.factorial(m) for m in c.values()))
    return math.factorial(n) // z


def tname(l):
    return "id" if not l else "_".join(map(str, l))


def lean_list(l):
    return "[" + ", ".join(map(str, l)) + "]"


class Family:
    def __init__(self, spec, n):
        w = spec.split(":")
        self.n = n
        if w[0] == "clique" and len(w) == 2:
            s = int(w[1])
            self.ns, self.args = "CliqueFreeFam", f"(n := {n}) (s := {s})"
            self.obj = f"{{G : SimpleGraph (Fin {n}) // G.CliqueFree {s}}}"
            self.prefix = f"tri{n}" if s == 3 else f"clique{s}_{n}"
            self.desc = f"graphs on {n} vertices without a {s}-clique"
            self.prop = f"G.CliqueFree {s}"
            self.member = f"cliqueFree_of_check _ {s} (by decide +kernel)"
        elif w[0] == "ramsey" and len(w) == 3:
            s, t = int(w[1]), int(w[2])
            self.ns, self.args = "RamseyFam", f"(n := {n}) (s := {s}) (t := {t})"
            self.obj = f"{{G : SimpleGraph (Fin {n}) // G.CliqueFree {s} ∧ Gᶜ.CliqueFree {t}}}"
            self.prefix = f"ramsey{s}{t}_{n}"
            self.desc = (f"graphs on {n} vertices without a {s}-clique and without an "
                         f"independent {t}-set")
            self.prop = f"G.CliqueFree {s} ∧ Gᶜ.CliqueFree {t}"
            self.member = (f"⟨cliqueFree_of_check _ {s} (by decide +kernel), "
                           f"compl_cliqueFree_of_check _ {t} (by decide +kernel)⟩")
        else:
            sys.exit(f"unknown family {spec}")

    def lemma(self, l):
        if l is None:  # the plain encoder
            return f"{self.ns}.card_of_check {self.args}"
        return f"{self.ns}.fix_card_of_check {self.args} (l := {lean_list(l)})"

    def thm(self, l):
        return self.prefix if not l else f"{self.prefix}_fix_{tname(l)}"

    def nbr_lemma(self, k):
        return f"{self.ns}.nbr_card_of_check {self.args} (k := {k})"

    def nbr_thm(self, k):
        return f"{self.prefix}_nbr_{k}"


HEADER = ["import CountCatcher", "import CountCatcherMath.Families.GraphIso", "",
          "open SimpleGraph CountCatcher CountCatcher.GraphIso CountCatcher.CycleType", ""]


def now():
    return time.time()


RSS = {}  # log file -> peak RSS in MB of the process tree (wait4)


def run(cmd, cwd, log, ok=(0,), env=None):
    """Run cmd with output to log; return (exit code, wall seconds). The peak RSS of the process
    and its waited-for descendants goes to RSS[log] (MB)."""
    t = now()
    with open(log, "w") as f:
        p = subprocess.Popen(cmd, cwd=cwd, stdout=f, stderr=subprocess.STDOUT, env=env)
        _, status, ru = os.wait4(p.pid, 0)
        code = os.waitstatus_to_exitcode(status)
    dt = now() - t
    RSS[log] = ru.ru_maxrss / (1 << 20 if platform.system() == "Darwin" else 1 << 10)
    if code not in ok:
        with open(log) as f:
            tail = f.read()[-1500:]
        raise RuntimeError(f"{' '.join(cmd[:2])} exit {code} in {cwd}:\n{tail}")
    return code, dt


def strip_tautologies(src, dst):
    clauses, cur, nv = [], [], 0
    with open(src) as f:
        for line in f:
            t = line.split()
            if not t or t[0] == "c":
                continue
            if t[0] == "p":
                nv = int(t[2])
                continue
            for x in map(int, t):
                if x == 0:
                    clauses.append(cur)
                    cur = []
                else:
                    cur.append(x)
    keep = [c for c in clauses if not any(-x in c for x in c)]
    with open(dst, "w") as f:
        f.write(f"p cnf {nv} {len(keep)}\n")
        for c in keep:
            f.write(" ".join(map(str, c)) + " 0\n")
    return len(clauses) - len(keep)


def files_arg(r, base=None):
    """The file arguments of count_models for a result of `certify`: the LRAT refutation
    (count 0), or the POG and LRAT files, with the keep file if the LRAT is numbered for it.
    base: the directory of the theorem file; the paths are then written relative to it
    (count_models resolves them against the directory of the source file), else absolute."""
    rel = (lambda p: os.path.relpath(p, base)) if base else (lambda p: p)
    return " ".join(f'"{rel(p)}"' for p in r["files"]) + (
        f' (keep := "{rel(r["keep"])}")' if r.get("keep") else "")


def certify(d, env, sat_first=None, embed_max=None, gen="struct", inline=None,
            gen_race="hybrid"):
    """D4, then the generator GEN_BIN + cpog2lrat (count > 0) or CaDiCaL (count 0), in directory d.
    With sat_first = T, CaDiCaL runs first with a time limit of T s; a refutation is the
    certificate and D4 is skipped. embed_max: the countCatcher.embedMaxBytes of the theorem file;
    count_models streams a text LRAT file larger than that, so such a certificate is translated
    again with --keep --binary (r["keep"]: the keep file, which files_arg passes along).
    gen: struct (cpog-gen's structural mode), mono (-m), hybrid (-M, -W) or race (structural
    against gen_race at once, gen_race.py; r["gen_winner"]). inline: cpog2lrat --inline
    (single-use additions inlined)."""
    r = {}
    with open(os.path.join(d, "in.cnf")) as f:
        hdr = next(l.split() for l in f if l.startswith("p"))
    r["vars"], r["clauses"] = int(hdr[2]), int(hdr[3])
    if sat_first:
        strip_tautologies(os.path.join(d, "in.cnf"), os.path.join(d, "in_nt.cnf"))
        code, dt = run(["timeout", str(sat_first), "cadical", "-q", "--lrat", "--no-binary",
                        "--no-factor", "in_nt.cnf", "unsat.lrat"], d,
                       os.path.join(d, "cadical.log"), ok=(10, 20, 124), env=env)
        if code == 20:
            r.update(count=0, kind="unsat", d4_s=0.0, gen_s=dt, d4_mb=0,
                     lrat_bytes=os.path.getsize(os.path.join(d, "unsat.lrat")),
                     files=[os.path.join(d, "unsat.lrat")])
            return r
        if os.path.exists(os.path.join(d, "unsat.lrat")):
            os.remove(os.path.join(d, "unsat.lrat"))
    _, r["d4_s"] = run(["d4", "in.cnf", "-dDNNF", "-out=in.nnf"], d, os.path.join(d, "d4.log"),
                       env=env)
    with open(os.path.join(d, "d4.log")) as f:
        m = re.search(r"^s (\d+)", f.read(), re.M)
    if not m:
        raise RuntimeError(f"no count from D4 in {d}")
    r["count"] = int(m.group(1))
    r["d4_mb"] = RSS[os.path.join(d, "d4.log")]
    if r["count"] == 0:
        strip_tautologies(os.path.join(d, "in.cnf"), os.path.join(d, "in_nt.cnf"))
        _, r["gen_s"] = run(["cadical", "-q", "--lrat", "--no-binary", "--no-factor",
                             "in_nt.cnf", "unsat.lrat"], d, os.path.join(d, "cadical.log"),
                            ok=(20,), env=env)
        r["kind"] = "unsat"
        r["lrat_bytes"] = os.path.getsize(os.path.join(d, "unsat.lrat"))
        r["files"] = [os.path.join(d, "unsat.lrat")]
        os.remove(os.path.join(d, "in.nnf"))
        return r
    from gen_race import mode_flags, race
    if gen == "race":
        g = race(GEN_BIN, GEN_FL, os.path.join(d, "in.cnf"), os.path.join(d, "in.nnf"), d,
                 env=env, contender=gen_race)
        if g["winner"] is None:
            raise RuntimeError(f"cpog-gen race in {d}: no mode succeeded ({g['exit']})")
        r["gen_s"], r["gen_winner"] = g["wall_s"], g["winner"]
        RSS[os.path.join(d, "gen.log")] = g["maxrss"] / (1 << 20 if platform.system() == "Darwin"
                                                         else 1 << 10)
    else:
        _, r["gen_s"] = run([GEN_BIN, *mode_flags(gen), *GEN_FL, "in.cnf", "in.nnf",
                             "cert.cpog"], d, os.path.join(d, "gen.log"), env=env)
    r["cpog_bytes"] = os.path.getsize(os.path.join(d, "cert.cpog"))
    r["gen_mb"] = RSS[os.path.join(d, "gen.log")]
    os.remove(os.path.join(d, "in.nnf"))
    # inline: None = only where the proof is streamed, True = always, False = never
    inl = ["--inline"] if inline else []
    inl_keep = [] if inline is False else ["--inline"]
    _, r["c2l_s"] = run(["cpog2lrat", "in.cnf", "cert.cpog", "fwd", "--delete", "--trim", *inl],
                        d, os.path.join(d, "c2l.log"), env=env)
    if embed_max is not None and os.path.getsize(os.path.join(d, "fwd.lrat")) > embed_max:
        _, dt = run(["cpog2lrat", "in.cnf", "cert.cpog", "fwd", "--delete", "--keep", "--binary",
                     *inl_keep], d, os.path.join(d, "c2l.log"), env=env)
        r["c2l_s"] += dt
        r["keep"] = os.path.join(d, "fwd.keep")
    for x in ("cert.cpog", "fwd.cnf"):
        if os.path.exists(os.path.join(d, x)):
            os.remove(os.path.join(d, x))
    for x in os.listdir(d):
        if x.startswith("reduction-"):
            os.remove(os.path.join(d, x))
    r["kind"] = "cpog"
    r["lrat_bytes"] = os.path.getsize(os.path.join(d, "fwd.lrat"))
    r["pog_bytes"] = os.path.getsize(os.path.join(d, "fwd.pog"))
    r["files"] = [os.path.join(d, "fwd.pog"), os.path.join(d, "fwd.lrat")]
    return r


def terms(fam, types, split):
    """The certified counts: (key, family lemma, theorem name, multiplicity)."""
    n = fam.n
    out = []
    for l in types:
        if not l and split:
            out += [(f"nbr_{k}", fam.nbr_lemma(k), fam.nbr_thm(k), math.comb(n - 1, k))
                    for k in range(n)]
        else:
            out.append((tname(l), fam.lemma(l if l else None), fam.thm(l), class_size(n, l)))
    return out


def chain(facts):
    c = "List.forall_mem_nil _"
    for f in reversed(facts):
        c = f"List.forall_mem_cons.2 ⟨{f},\n      {c}⟩"
    return c


# ---- the labelled count as a tree of cell splits (--tree) ----------------------------------
#
# A node is a pattern (u, v, b) of fixed adjacencies (GraphIso.Sat). The root (empty pattern)
# is split by the neighbourhood of vertex 0 in C = [1..n-1] (child k: N(0) = {1..k}); a child k
# listed in --tree is refined inside S = {1..k}: the vertices 1, 2, ... of S are individualized
# in turn and every current cell of S is split by the neighbourhood of that vertex
# (GraphIso.card_eq_of_cell, multiplicity C(|C|, j)). CaDiCaL decides each node during the
# construction: UNSAT gives a leaf (its LRAT refutation), otherwise the node is split further,
# until G[S] is fixed. Fully refined leaves that are equal up to relabelling share one
# certificate (GraphIso.card_sat_iso).

def star(v, C, j):
    return [(v, c, i < j) for i, c in enumerate(C)]


def edge_index(n):
    return {e: k for k, e in enumerate((i, j) for i in range(n) for j in range(i + 1, n))}


class Node:
    def __init__(self, nid, parent, how, state):
        self.id, self.parent, self.how, self.state = nid, parent, how, state
        self.pat = (parent.pat if parent else []) + (star(*how) if how else [])
        self.kind = None      # split | unsat | count | iso
        self.split = None     # (v, C)
        self.children = []
        self.count = None
        self.iso = None       # (canonical node, swaps)
        self.sat_s = None


def pick(cells):
    """Individualize the first vertex of the first cell; None if nothing is left to split."""
    if not cells:
        return None
    v = cells[0][0]
    rest = [c for c in [cells[0][1:]] + cells[1:] if c]
    return (v, [], rest) if rest else None


def advance(state, j):
    v, done, todo = state
    C = todo[0]
    done = done + [c for c in (C[:j], C[j:]) if c]
    return (v, done, todo[1:]) if todo[1:] else pick(done)


def find_iso(pa, pb):
    """A vertex map s with relabel s pa = pb (entries up to orientation), or None."""
    def amap(pat):
        m = {}
        for u, w, b in pat:
            m[frozenset((u, w))] = b
        return m
    A, B = amap(pa), amap(pb)
    if len(A) != len(B):
        return None
    adjA, adjB = {}, {}
    for adj, M in ((adjA, A), (adjB, B)):
        for e, b in M.items():
            u, w = tuple(e)
            adj.setdefault(u, {})[w] = b
            adj.setdefault(w, {})[u] = b
    sig = lambda adj, u: (sum(adj[u].values()), len(adj[u]))
    va = sorted(adjA, key=lambda u: -len(adjA[u]))
    vb = list(adjB)
    if sorted(sig(adjA, u) for u in va) != sorted(sig(adjB, u) for u in vb):
        return None
    s, used = {}, set()

    def rec(i):
        if i == len(va):
            return True
        a = va[i]
        for b in vb:
            if b in used or sig(adjA, a) != sig(adjB, b):
                continue
            if all(adjA[a].get(a2) == adjB[b].get(s[a2]) for a2 in s):
                s[a] = b
                used.add(b)
                if rec(i + 1):
                    return True
                del s[a]
                used.discard(b)
        return False
    return dict(s) if rec(0) else None


def to_swaps(s):
    """Transpositions whose product (Lean List.prod, rightmost applied first) is the map s."""
    out, seen = [], set()
    for a in sorted(s):
        if a in seen or s[a] == a:
            continue
        cyc, x = [], a
        while x not in seen:
            seen.add(x)
            cyc.append(x)
            x = s[x]
        out += [(cyc[0], c) for c in reversed(cyc[1:])]
    # check: apply the product right to left
    for a in s:
        x = a
        for (p, q) in reversed(out):
            x = q if x == p else p if x == q else x
        assert x == s[a], "swap decomposition"
    return out


def explore(n, ks, base, work, env, jobs, sat_timeout):
    """Build the tree; returns the list of nodes (root first, parents before children)."""
    E = edge_index(n)
    nodes = []

    def mk(parent, how, state):
        nd = Node(len(nodes), parent, how, state)
        nodes.append(nd)
        d = os.path.join(work, f"t{nd.id}")
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "in.cnf"), "w") as f:
            f.write(f"p cnf {base[0]} {len(base[1]) + len(nd.pat)}\n")
            f.writelines(base[1])
            for u, w, b in nd.pat:
                x = E[(min(u, w), max(u, w))] + 1
                f.write(f"{x if b else -x} 0\n")
        return nd

    root = mk(None, None, None)
    root.kind, root.split = "split", (0, list(range(1, n)))
    pending = []
    for k in range(n):
        nd = mk(root, (0, root.split[1], k), pick([list(range(1, k + 1))]) if k in ks else None)
        root.children.append(nd)
        if k in ks and nd.state is not None:
            pending.append(nd)
        else:
            nd.kind = "count"

    def decide_node(nd):
        d = os.path.join(work, f"t{nd.id}")
        strip_tautologies(os.path.join(d, "in.cnf"), os.path.join(d, "in_nt.cnf"))
        code, dt = run(["timeout", str(sat_timeout), "cadical", "-q", "--lrat", "--no-binary",
                        "--no-factor", "in_nt.cnf", "unsat.lrat"], d,
                       os.path.join(d, "cadical.log"), ok=(10, 20, 124), env=env)
        if code != 20 and os.path.exists(os.path.join(d, "unsat.lrat")):
            os.remove(os.path.join(d, "unsat.lrat"))
        return code, dt

    level = 0
    while pending:
        level += 1
        t0 = now()
        with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
            out = list(ex.map(decide_node, pending))
        nxt = []
        for nd, (code, dt) in zip(pending, out):
            nd.sat_s = dt
            if code == 20:
                nd.kind = "unsat"
                continue
            v, todo = nd.state[0], nd.state[2]
            nd.kind, nd.split = "split", (v, todo[0])
            for j in range(len(todo[0]) + 1):
                ch = mk(nd, (v, todo[0], j), advance(nd.state, j))
                nd.children.append(ch)
                if ch.state is None:
                    ch.kind = "count"
                else:
                    nxt.append(ch)
        print(f"graph_orbits: tree level {level}: {len(pending)} nodes decided in "
              f"{now() - t0:.1f} s, {sum(1 for c in out if c[0] == 20)} unsat, "
              f"{sum(1 for c in out if c[0] == 10)} sat, {sum(1 for c in out if c[0] == 124)} "
              f"timeout", flush=True)
        pending = nxt
    # leaves equal up to relabelling share a certificate
    canon = []
    for nd in nodes:
        if nd.kind != "count" or nd.state is not None or nd.parent is root:
            continue
        for c in canon:
            s = find_iso(nd.pat, c.pat)
            if s is not None:
                nd.kind, nd.iso = "iso", (c, to_swaps(s))
                break
        else:
            canon.append(nd)
    return nodes


def tree_counts(nodes, res):
    for nd in nodes:
        if nd.kind in ("count", "unsat"):
            nd.count = res[f"t{nd.id}"]["count"]
    for nd in nodes:
        if nd.kind == "iso":
            nd.count = nd.iso[0].count
    for nd in reversed(nodes):
        if nd.kind == "split":
            nd.count = sum(math.comb(len(nd.split[1]), ch.how[2]) * ch.count
                           for ch in nd.children)
    return nodes[0].count


def pattern_defs(fam, nodes):
    P, n = fam.prefix, fam.n
    out = []
    for nd in nodes:
        if nd.parent is None:
            out.append(f"def {P}_p0 : GraphIso.Pattern {n} := []")
        else:
            v, C, j = nd.how
            out.append(f"def {P}_p{nd.id} : GraphIso.Pattern {n} := {P}_p{nd.parent.id} ++ "
                       f"GraphIso.star {v} {lean_list(C)} {j}")
    return out


def tree_lean(fam, nodes, res, labelled, base=None):
    P, ns, args = fam.prefix, fam.ns, fam.args
    st = lambda nd: f"Nat.card {{x : {fam.obj} // GraphIso.Sat x.1 {P}_p{nd.id}}} = {nd.count}"
    out = ["", "/-! The labelled count as a tree of cell splits (`GraphIso.card_eq_of_cell`). -/", ""]
    out += pattern_defs(fam, nodes) + [""]
    for nd in nodes:
        if nd.kind in ("count", "unsat"):
            r = res[f"t{nd.id}"]
            hint = f" (count := {r['count']})" if r["count"] > 0 else ""
            out.append(f"count_models {P}_t{nd.id} via ({ns}.cube_card_of_check {args} "
                       f"(α := {P}_p{nd.id})) {files_arg(r, base)}{hint}")
    out.append("")
    for nd in nodes:
        if nd.kind == "iso":
            c, sw = nd.iso
            out += [f"theorem {P}_t{nd.id} : {st(nd)} :=",
                    f"  {ns}.card_sat_iso {args} (GraphIso.swaps "
                    f"[{', '.join(f'({a}, {b})' for a, b in sw)}]) (by decide +kernel) {P}_t{c.id}",
                    ""]
    for nd in reversed(nodes):
        if nd.kind == "split":
            v, C = nd.split
            entries = ", ".join(f"({ch.how[2]}, {ch.count})" for ch in nd.children)
            out += [f"theorem {P}_t{nd.id} : {st(nd)} :=",
                    f"  {ns}.card_eq_of_cell {args} {P}_p{nd.id} {v} {lean_list(C)} {nd.count}",
                    f"    [{entries}]",
                    f"    ({chain([f'{P}_t{ch.id}' for ch in nd.children])})",
                    "    (by decide +kernel)", ""]
    out += [f"/-- The labelled count, from the tree of cell splits. -/",
            f"theorem {P} : Nat.card {fam.obj} = {labelled} :=",
            f"  {ns}.card_of_root {args} {P}_t0", ""]
    return out


def theorem_file(fam, types, res, orbits, embed_max, split, labelled, witness=None, tree=None,
                 base=None):
    n = fam.n
    out = HEADER + [f"set_option countCatcher.embedMaxBytes {embed_max}", "set_option maxRecDepth 100000", ""]
    if tree:
        out += tree_lean(fam, tree, res, labelled, base)
    for key, lem, thm, _ in terms(fam, [l for l in types if l or not tree], split):
        r = res[key]
        hint = f" (count := {r['count']})" if r["count"] > 0 else ""
        out.append(f"count_models {thm} via ({lem}) {files_arg(r, base)}{hint}")
    if split:
        entries = [f"({k}, {res[f'nbr_{k}']['count']})" for k in range(n)]
        out += ["",
                f"/-- The labelled count, from the counts per neighbourhood of vertex `0`. -/",
                f"theorem {fam.prefix} : Nat.card {fam.obj} = {labelled} :=",
                f"  {fam.ns}.card_eq_of_split {labelled}",
                "    [" + ",\n     ".join(entries) + "]",
                f"    ({chain([fam.nbr_thm(k) for k in range(n)])})",
                "    (by decide)"]
    # Burnside assembly
    entries = [f"({lean_list(l)}, {res[tname(l)]['count']})" for l in types]
    facts = [f"{fam.ns}.fix_nil {fam.thm(l)}" if not l else fam.thm(l) for l in types]
    name = f"{fam.prefix}_orbits"
    out += ["",
            f"/-- The number of {fam.desc}, up to relabelling (orbits of `Perm (Fin {n})`), by",
            "    Burnside's lemma over the cycle types from the certified counts above. -/",
            f"theorem {name} :",
            f"    Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin {n}))",
            f"      {fam.obj}) = {orbits} :=",
            f"  {fam.ns}.card_orbits_eq {orbits}",
            "    [" + ",\n     ".join(entries) + "]",
            f"    ({chain(facts)})",
            "    (by decide)",
            "",
            f"/-- The number of isomorphism classes of {fam.desc}. -/",
            f"theorem {fam.prefix}_isoClasses :",
            f"    Nat.card (Quot fun G H : {fam.obj} => Nonempty (G.1 ≃g H.1)) = {orbits} :=",
            f"  {fam.ns}.card_isoClasses_eq {name}"]
    if witness and orbits == 1:
        out += ["",
                f"/-- Every graph in the family is isomorphic to `{witness}`. -/",
                f"theorem {fam.prefix}_unique (G : SimpleGraph (Fin {n})) (h : {fam.prop}) :",
                f"    Nonempty (G ≃g {witness}) :=",
                f"  iso_of_card_isoClasses_eq_one {fam.prefix}_isoClasses ⟨G, h⟩",
                f"    ⟨{witness}, {fam.member}⟩",
                "",
                f"#print axioms {fam.prefix}_unique"]
    out += ["",
            f"#print axioms {name}",
            f"#print axioms {fam.prefix}_isoClasses",
            f"#print axioms {fam.prefix}"]
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--family", required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--out")
    ap.add_argument("--work")
    ap.add_argument("--lean", default=os.path.join(REPO, "lean"))
    ap.add_argument("--tools", default=os.path.join(REPO, "tools", "bin"))
    ap.add_argument("-j", type=int, default=4)
    ap.add_argument("--embed-max", type=int, default=64 << 20)
    ap.add_argument("--split", action="store_true",
                    help="split the identity term by the neighbourhood of vertex 0")
    ap.add_argument("--witness", help="Lean term of a graph in the family; if there is one class,"
                    " the theorem file also proves that every graph is isomorphic to it")
    ap.add_argument("--tree", help="K[,K...]: the labelled count as a tree of cell splits; the "
                    "children N(0) = {1..K} are refined inside {1..K} (GraphIso.card_eq_of_cell)")
    ap.add_argument("--tree-sat-timeout", type=int, default=120,
                    help="CaDiCaL time limit per tree node during the construction (s)")
    ap.add_argument("--sat-first", type=int, metavar="T",
                    help="try a CaDiCaL refutation (T s) before D4 for every term")
    ap.add_argument("--gen", choices=["struct", "mono", "hybrid", "race"], default="struct",
                    help="certificate generation: structural (default), monolithic (-m), hybrid "
                    "(-M, -W), or structural against --gen-race at once, the first to finish "
                    "wins (gen_race.py)")
    ap.add_argument("--gen-race", choices=["hybrid", "mono"], default="hybrid",
                    help="the race's contender (default hybrid)")
    ap.add_argument("--inline", action="store_true",
                    help="cpog2lrat --inline also for embedded terms (default: streamed terms only)")
    ap.add_argument("--no-inline", action="store_true", help="never pass --inline to cpog2lrat")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--no-lean", action="store_true")
    ap.add_argument("--only-export", action="store_true")
    ap.add_argument("--reuse-export", action="store_true",
                    help="skip the export when every formula file exists in WORK")
    ap.add_argument("--only-tree", action="store_true", help="stop after building the tree")
    ap.add_argument("--append", help="Lean file whose text is appended to the theorem file")
    a = ap.parse_args()
    fam = Family(a.family, a.n)
    n = a.n
    out = os.path.abspath(a.out or os.path.join("graph-orbits", fam.prefix))
    work = os.path.abspath(a.work or os.path.join(out, "work"))
    os.makedirs(out, exist_ok=True)
    os.makedirs(work, exist_ok=True)
    env = dict(os.environ, PATH=a.tools + os.pathsep + os.environ.get("PATH", ""))
    plugins = [
        f"--plugin={a.lean}/.lake/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.{EXT}",
        f"--plugin={a.lean}/.lake/build/lib/libCountCatcher_CountCatcherChecker.{EXT}"]
    kv = open(os.path.join(out, "result.txt"), "w")

    def put(k, v):
        kv.write(f"{k}={v}\n")
        kv.flush()

    put("family", a.family)
    put("n", n)
    put("host", platform.node())
    types = cycle_types(n)
    assert sum(class_size(n, l) for l in types) == math.factorial(n)
    put("cycle_types", len(types))
    put("split", int(a.split))
    ks = set(int(k) for k in a.tree.split(",") if k) if a.tree is not None else None
    if ks is not None:
        if a.split:
            sys.exit("--tree replaces --split")
        put("tree", ",".join(map(str, sorted(ks))))
    # with --tree the plain encoder is exported only as the base of the tree's cube formulas
    tl = terms(fam, [l for l in types if l or ks is None], a.split)
    exported = tl + ([("id", fam.lemma(None), fam.thm([]), 1)] if ks is not None else [])
    for key, _, _, _ in exported:
        os.makedirs(os.path.join(work, key), exist_ok=True)

    # 1. export all formulas from the Lean terms, in one Lean run
    if a.reuse_export and all(os.path.exists(os.path.join(work, key, "in.cnf"))
                              for key, _, _, _ in exported):
        put("export_s", "reused")
    else:
        exp = os.path.join(work, "export.lean")
        with open(exp, "w") as f:
            f.write("\n".join(HEADER) + "\n")
            for key, lem, _, _ in exported:
                p = os.path.join(work, key, "in.cnf")
                f.write(f'#export_cnf via ({lem}) "{p}"\n')
        _, dt = run(["lake", "env", "lean", *plugins, exp], a.lean,
                    os.path.join(out, "export.out"), env=env)
        put("export_s", f"{dt:.1f}")
    if a.only_export:
        return

    # 1b. the tree: construction with CaDiCaL, then the leaf formulas exported from Lean and
    #     compared with the ones the construction wrote
    tree, res = None, {}
    if ks is not None:
        with open(os.path.join(work, "id", "in.cnf")) as f:
            lines = f.readlines()
        hdr = next(l.split() for l in lines if l.startswith("p"))
        base = (int(hdr[2]), [l for l in lines if l.strip() and l[0] not in "cp"])
        assert len(base[1]) == int(hdr[3])
        t0 = now()
        tree = explore(n, ks, base, work, env, a.j, a.tree_sat_timeout)
        put("tree_wall_s", f"{now() - t0:.1f}")
        kinds = Counter(nd.kind for nd in tree)
        put("tree_nodes", len(tree))
        for k in ("split", "unsat", "count", "iso"):
            put(f"tree_{k}", kinds.get(k, 0))
        with open(os.path.join(out, "tree.tsv"), "w") as f:
            f.write("id\tparent\thow\tkind\tsat_s\tentries\n")
            for nd in tree:
                f.write(f"{nd.id}\t{nd.parent.id if nd.parent else ''}\t{nd.how}\t{nd.kind}\t"
                        f"{'' if nd.sat_s is None else f'{nd.sat_s:.2f}'}\t{len(nd.pat)}\n")
        leaves = [nd for nd in tree if nd.kind in ("count", "unsat")]
        exp2 = os.path.join(work, "export_tree.lean")
        with open(exp2, "w") as f:
            f.write("\n".join(HEADER + pattern_defs(fam, tree)) + "\n")
            for nd in leaves:
                p = os.path.join(work, f"t{nd.id}", "lean.cnf")
                f.write(f'#export_cnf via ({fam.ns}.cube_card_of_check {fam.args} '
                        f'(α := {fam.prefix}_p{nd.id})) "{p}"\n')
        _, dt = run(["lake", "env", "lean", *plugins, exp2], a.lean,
                    os.path.join(out, "export_tree.out"), env=env)
        put("export_tree_s", f"{dt:.1f}")
        for nd in leaves:
            d = os.path.join(work, f"t{nd.id}")
            if not filecmp.cmp(os.path.join(d, "in.cnf"), os.path.join(d, "lean.cnf"),
                               shallow=False):
                sys.exit(f"tree leaf t{nd.id}: the written formula differs from Lean's")
            if nd.kind == "unsat":
                res[f"t{nd.id}"] = {"kind": "unsat", "count": 0, "vars": base[0],
                                    "clauses": len(base[1]) + len(nd.pat), "d4_s": 0.0,
                                    "gen_s": nd.sat_s, "d4_mb": 0,
                                    "lrat_bytes": os.path.getsize(os.path.join(d, "unsat.lrat")),
                                    "files": [os.path.join(d, "unsat.lrat")]}
        print(f"graph_orbits: tree: {dict(kinds)}, leaf formulas agree with Lean", flush=True)
        if a.only_tree:
            return

    # 2. certificates, largest (identity) first
    todo = [key for key, _, _, _ in tl]
    if tree:
        todo = [f"t{nd.id}" for nd in tree if nd.kind == "count"] + todo
    t0 = now()
    with cf.ThreadPoolExecutor(max_workers=a.j) as ex:
        futs = {ex.submit(certify, os.path.join(work, key), env, a.sat_first, a.embed_max,
                          a.gen, True if a.inline else (False if a.no_inline else None),
                          a.gen_race): key for key in todo}
        for fu in cf.as_completed(futs):
            key = futs[fu]
            res[key] = r = fu.result()
            print(f"graph_orbits: {key}: count {r['count']} ({r['kind']}), "
                  f"d4 {r['d4_s']:.1f} s, gen {r['gen_s']:.1f} s"
                  + (f" ({r['gen_winner']} won)" if "gen_winner" in r else ""), flush=True)
    put("certify_wall_s", f"{now() - t0:.1f}")
    put("masked", sum(1 for r in res.values() if r.get("keep")))  # streamed with a keep file
    if a.split:
        res["id"] = {"count": sum(math.comb(n - 1, k) * res[f"nbr_{k}"]["count"]
                                  for k in range(n))}
    if tree:
        res["id"] = {"count": tree_counts(tree, res)}
    total = sum(class_size(n, l) * res[tname(l)]["count"] for l in types)
    if total % math.factorial(n):
        sys.exit(f"Burnside sum {total} not divisible by {n}!")
    orbits = total // math.factorial(n)
    put("labelled", res["id"]["count"])
    put("orbits", orbits)
    print(f"graph_orbits: {len(types)} cycle types, labelled {res['id']['count']}, "
          f"orbits {orbits}", flush=True)

    # 3. theorem file
    thy = os.path.join(work, "T.lean")
    with open(thy, "w") as f:
        f.write(theorem_file(fam, types, res, orbits, a.embed_max, a.split, res["id"]["count"],
                             a.witness, tree, base=work))
        if a.append:
            f.write("\n" + open(a.append).read())
    shutil.copy(thy, os.path.join(out, "T.lean"))

    # 4. Lean
    lean_ms = {}
    if not a.no_lean:
        e, dt = run(["lake", "env", "lean", *plugins, thy], a.lean, os.path.join(out, "lean.out"),
                    ok=(0, 1), env=env)
        put("lean_exit", e)
        put("lean_s", f"{dt:.1f}")
        put("lean_peak_mb", f"{RSS[os.path.join(out, 'lean.out')]:.0f}")
        txt = open(os.path.join(out, "lean.out")).read()
        for m in re.finditer(r"count_models (\S+): (.*)", txt):
            lean_ms[m.group(1)] = m.group(2)
        proved = (e == 0 and "error" not in txt
                  and f"'{fam.prefix}_orbits' depends on axioms" in txt)
        put("status", "proved" if proved else "lean_fail")
    # 5. summary
    with open(os.path.join(out, "summary.tsv"), "w") as f:
        f.write("type\tclass_size\tcount\tkind\tvars\tclauses\td4_s\tgen_s\tc2l_s\tcpog_bytes"
                "\tlrat_bytes\td4_mb\tgen_mb\tlean\n")
        rows = list(tl)
        if tree:
            def mult(nd):
                m = 1
                while nd.parent is not None:
                    m *= math.comb(len(nd.how[1]), nd.how[2])
                    nd = nd.parent
                return m
            rows = [(f"t{nd.id}", None, f"{fam.prefix}_t{nd.id}", mult(nd))
                    for nd in tree if nd.kind in ("count", "unsat")] + rows
        for key, _, thm, mult in rows:
            r = res[key]
            f.write("\t".join(str(x) for x in [
                key, mult, r["count"], r["kind"], r["vars"], r["clauses"],
                f"{r['d4_s']:.2f}", f"{r['gen_s']:.2f}", f"{r.get('c2l_s', 0):.2f}",
                r.get("cpog_bytes", 0), r["lrat_bytes"], f"{r['d4_mb']:.0f}",
                f"{r.get('gen_mb', 0):.0f}", lean_ms.get(thm, "")]) + "\n")
    if not a.keep and not a.no_lean and "proved" in open(os.path.join(out, "result.txt")).read():
        shutil.rmtree(work, ignore_errors=True)
        put("work_deleted", work)
    kv.close()


if __name__ == "__main__":
    main()

"""Reduced Latin squares of order n as a Lean theorem through the cycle types of the second row
(CountCatcherMath/Families/LatinCycle.lean).

The fibre count of an admissible second row r (r[0] = 1, r[j] != j) depends only on the cycle
type of r as a permutation (Latin.card_fibre_eq_of_conj). One representative per type, the
lexicographically first admissible row of that type, is certified; every admissible row gets a
permutation s with q[s[j]] = s[r[j]] onto its representative q (cycles of r mapped onto cycles of
q of the same length, in order). The assembly Latin.card_eq_of_classes checks the row list
against Latin.rows n and every s by decide +kernel, and sums class size times fibre count.

A representative's fibre is certified directly (leaf Latin.fibre_card_of_check) or, with --k K,
split by the cells (2, 1), ..., (2, K) of the third row into the parts Latin.cellCnf n r t, one
leaf for each t in Latin.thirdRows n r K (Latin.fibre_card_eq_of_cells).

Modes:
  --plan-only     write OUT/plan.json (read by the other modes) and the views OUT/plan.tsv,
                  OUT/classes.tsv, OUT/assign.tsv; with --pilot-d4 TSV (name, count, nnf_bytes of
                  the D4 pilot, names tTYPE_kK_IIII) also the expected count and .nnf size of each
                  leaf and the index lists OUT/tier_small.txt, OUT/tier_large.txt (.nnf at most /
                  above --tier-mb MB) for two memory tiers of the array job
  --leaf I        leaf I of the plan (--plan FILE, default OUT/plan.json; OUT is its directory):
                  export its formula from the Lean term (#export_cnf via its lemma), D4, then
                  cpog-gen-fwd -F -T 500 -G and the native cpog2lrat --delete --keep --binary (--inline
                  only with --inline), or CaDiCaL if the count is 0; then the leaf theorem
                  (count_models, streamed with the keep mask) compiled to its own module
                  MOD/<Pkg>/<leaf>.olean with `lean -R MOD -o` (--mod MOD, default OUT/mod; the
                  .olean holds the POG text and the keep mask, about the leaf's .nnf size, since
                  the theorem's proof refers to them); certificates in
                  --scratch DIR (default $SLURM_TMPDIR, else OUT/work), deleted after the Lean
                  check (--keep-cert keeps them). Result OUT/res/<leaf>.txt (key=value: per stage
                  seconds, exit code, peak RSS of the child in MB; bytes; counts; status). A leaf
                  whose result says status=proved is skipped.
                  With --plan and --out, the results go to OUT instead of the plan's directory
                  (a rerun of one leaf of a finished plan).
  --assemble      read every OUT/res/<leaf>.txt (all must say status=proved, and the count must
                  equal the plan's expected count where one is given), write OUT/mod/T.lean (the
                  fibre theorems, P_reduced by Latin.card_eq_of_classes, P_all by
                  Latin.card_latin_eq; it imports every leaf module) and check it.
                  Result OUT/assemble.txt.
  --assemble-hyp  P_all with the leaf counts as hypotheses, one per fibre class (the hypothesis
                  hT of Latin.fibre_card_eq_of_cells over the class's list of parts and counts,
                  read from the plan directory's res/<leaf>.txt): coverage, sums and the class
                  assignment are checked by decide +kernel without certificates or leaf modules.
                  File --hyp-out (default OUT/P_all.lean), with .txt (key=value) and .out next
                  to it.
  --single        (with --n, --k 0) one theorem file OUT/P.lean, as in the paper's listing: each
                  fibre by the count-catcher driver (scripts/count_catcher.py P_fibreI --via
                  'Latin.fibre_card_of_check ...' --dir OUT/cI), its count_models line copied
                  with the paths relative to OUT ("c0/fwd.pog"), then P_reduced and P_all;
                  checked with Lean. Result OUT/assemble.txt, certificates kept in OUT/cI.
  (none)          plan, every leaf in turn, assemble (local runs).
Theorem names (P = the plan's prefix latinN): P_fibreI for a whole fibre of class I, P_cI_JJJJ for a
part of a split fibre, P_fibreI for a split fibre's sum, P_reduced, P_all. Certificate paths in the
theorem files are relative to the file's directory (count_models resolves them against it).

Usage:
  uv run scripts/showcase/latin_cycles.py --n 7 --out DIR --single           (the paper's order 7)
  uv run scripts/showcase/latin_cycles.py --n 7 [--k K] [--split TYPES] --out DIR --plan-only
  uv run scripts/showcase/latin_cycles.py --plan DIR/plan.json --leaf 3 [--scratch S] [--inline]
  uv run scripts/showcase/latin_cycles.py --plan DIR/plan.json --assemble
  uv run scripts/showcase/latin_cycles.py --plan research/latin8-2026-10-04/plan.json --assemble-hyp \
      --out OUT                                       (order 8 from the 737 leaf counts)
  uv run scripts/showcase/latin_cycles.py --plan research/latin8-2026-10-04/plan.json --leaf 653 \
      --out OUT                                       (rerun one leaf of order 8, here c6_0025)
  Common: --lean LEANDIR (needs CountCatcher built) --tools TOOLSDIR --to-d4 --to-gen --to-lean.
  --split: the cycle types to split (e.g. "7;5,2"), default all types when --k > 0.
Paths are resolved with os.path.realpath before `lean -R ROOT -o`: lean derives the module name
from the source path relative to ROOT, so a symlinked component in one of them (e.g. /tmp and
/private/tmp on the Mac) would give the wrong module name.
"""

import argparse
import itertools
import json
import math
import os
import platform
import re
import shutil
import signal
import socket
import subprocess
import sys
import time
from collections import OrderedDict

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
EXT = "dylib" if platform.system() == "Darwin" else "so"
REDUCED = {5: 56, 6: 9408, 7: 16942080, 8: 535281401856}
GEN = ["cpog-gen-fwd", "-F", "-T", "500", "-G"]  # the certificate generator and its options
HEADER = ["import CountCatcherMath.Command", "import CountCatcherMath.Families.LatinCycle", "",
          "open CountCatcher", ""]


# ---------------------------------------------------------------- plan

def admissible_rows(n):
    """Second rows of reduced squares, in the order of Latin.rows n (lexicographic)."""
    return [p for p in itertools.permutations(range(n))
            if p[0] == 1 and all(p[j] != j for j in range(n))]


def cycles(p):
    seen, out = [False] * len(p), []
    for i in range(len(p)):
        if not seen[i]:
            c, j = [], i
            while not seen[j]:
                seen[j] = True
                c.append(j)
                j = p[j]
            out.append(c)
    return out


def ctype(p):
    return tuple(sorted((len(c) for c in cycles(p)), reverse=True))


def conj_perm(r, q):
    """A permutation s with q[s[j]] = s[r[j]]: each cycle of r onto a cycle of q of the same
    length (both in order of their smallest element), element by element."""
    free = {}
    for c in cycles(q):
        free.setdefault(len(c), []).append(c)
    s = [None] * len(r)
    for c in cycles(r):
        d = free[len(c)].pop(0)
        for i, x in enumerate(c):
            s[x] = d[i]
    assert all(q[s[j]] == s[r[j]] for j in range(len(r))) and sorted(s) == list(range(len(r)))
    return s


def third_rows(n, r, k):
    """Latin.thirdRows n r k: values of the cells (2, 1..k), distinct, cell (2, c) not c, not
    r[c], not 2; lexicographic (the order of Latin.seqs)."""
    out = []

    def rec(c, cur):
        if c == k + 1:
            out.append(list(cur))
            return
        for v in range(n):
            if v != c and v != r[c] and v != 2 and v not in cur:
                cur.append(v)
                rec(c + 1, cur)
                cur.pop()
    rec(1, [])
    return out


def plan(n, k, split):
    rows = admissible_rows(n)
    types = OrderedDict()
    for p in rows:  # lexicographic, so the first of each type is its representative
        types.setdefault(ctype(p), []).append(p)
    classes = [(t, ps[0], len(ps)) for t, ps in types.items()]
    index = {t: i for i, (t, _, _) in enumerate(classes)}
    assign = [(p, conj_perm(p, classes[index[ctype(p)]][1]), index[ctype(p)]) for p in rows]
    leaves = []  # (name, class index, rep, t or None)
    for i, (t, q, _) in enumerate(classes):
        if k > 0 and (split is None or t in split):
            for j, cells in enumerate(third_rows(n, q, k)):
                leaves.append((f"c{i}_{j:04d}", i, q, cells))
        else:
            leaves.append((f"c{i}_fibre", i, q, None))
    return rows, classes, assign, leaves


def vec(p):
    return "![" + ", ".join(map(str, p)) + "]"


def lst(p):
    return "[" + ", ".join(map(str, p)) + "]"


def tname(t):
    return "".join(map(str, t))


def chain(facts):
    c = "List.forall_mem_nil _"
    for f in reversed(facts):
        c = f"List.forall_mem_cons.2 ⟨{f},\n      {c}⟩"
    return c


def write_plan(a, out):
    n, k = a.n, a.k
    split = None if a.split is None else [
        [int(x) for x in s.split(",")] for s in a.split.split(";")]
    rows, classes, assign, leaves = plan(n, k, None if split is None else {tuple(s) for s in split})
    pilot = {}
    if a.pilot_d4:
        with open(a.pilot_d4) as f:
            hdr = f.readline().rstrip("\n").split("\t")
            for line in f:
                d = dict(zip(hdr, line.rstrip("\n").split("\t")))
                pilot[d["name"]] = (int(d["count"]), int(d["nnf_bytes"]))
    P = {"n": n, "k": k, "split": split, "prefix": f"latin{n}", "pkg": f"Latin{n}Cyc",
         "classes": [{"type": list(t), "rep": list(q), "size": size} for t, q, size in classes],
         "assign": [[list(p), list(s), i] for p, s, i in assign], "leaves": []}
    for idx, (name, i, q, t) in enumerate(leaves):
        e = {"index": idx, "name": name, "class": i, "rep": list(q), "cells": t}
        tag = "t" + "".join(map(str, classes[i][0]))
        j = int(name.split("_")[1]) if t is not None else None
        key = f"{tag}_k{k}_{j:04d}" if t is not None else None
        if key in pilot:
            e["count_d4"], e["nnf_bytes"] = pilot[key]
        P["leaves"].append(e)
    with open(os.path.join(out, "plan.json"), "w") as f:
        json.dump(P, f)
    with open(os.path.join(out, "classes.tsv"), "w") as f:
        f.write("class\ttype\tsize\trep\tleaves\n")
        for i, (t, q, size) in enumerate(classes):
            f.write(f"{i}\t{','.join(map(str, t))}\t{size}\t{tname(q)}\t"
                    f"{sum(1 for l in leaves if l[1] == i)}\n")
    with open(os.path.join(out, "assign.tsv"), "w") as f:
        f.write("row\tsigma\tclass\n")
        for p, s, i in assign:
            f.write(f"{tname(p)}\t{tname(s)}\t{i}\n")
    with open(os.path.join(out, "plan.tsv"), "w") as f:
        f.write("index\tleaf\tclass\trep\tcells\tcount_d4\tnnf_bytes\n")
        for e in P["leaves"]:
            f.write(f"{e['index']}\t{e['name']}\t{e['class']}\t{tname(e['rep'])}\t"
                    f"{'' if e['cells'] is None else tname(e['cells'])}\t"
                    f"{e.get('count_d4', '')}\t{e.get('nnf_bytes', '')}\n")
    if pilot:
        small = [e["index"] for e in P["leaves"] if e.get("nnf_bytes", 0) <= a.tier_mb * 1e6]
        large = [e["index"] for e in P["leaves"] if e.get("nnf_bytes", 0) > a.tier_mb * 1e6]
        for fn, l in (("tier_small.txt", small), ("tier_large.txt", large)):
            with open(os.path.join(out, fn), "w") as f:
                f.write(",".join(map(str, l)) + "\n")
        print(f"latin_cycles: tiers at {a.tier_mb} MB .nnf: {len(small)} small, {len(large)} large")
    print(f"latin_cycles: n={n} rows={len(rows)} classes={len(classes)} leaves={len(leaves)}")
    for i, (t, q, size) in enumerate(classes):
        print(f"  class {i}: type {list(t)} size {size} rep {tname(q)} "
              f"leaves {sum(1 for l in leaves if l[1] == i)}")
    return P


# ---------------------------------------------------------------- running

def stage(res, name, cmd, cwd, timeout, out, env=None):
    """Run cmd in its own process group, output to out; record NAME_s, NAME_exit and
    NAME_rss_mb (peak RSS of the child, os.wait4). Returns ok | timeout | killed | failN."""
    t = time.time()
    with open(out, "w") as f:
        p = subprocess.Popen(cmd, cwd=cwd, stdout=f, stderr=subprocess.STDOUT, env=env,
                             start_new_session=True)
        timed_out = False
        while True:
            pid, status, ru = os.wait4(p.pid, os.WNOHANG)
            if pid != 0:
                break
            if timeout and time.time() - t > timeout:
                timed_out = True
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                pid, status, ru = os.wait4(p.pid, 0)
                break
            time.sleep(0.2)
    code = os.waitstatus_to_exitcode(status)
    res[f"{name}_s"] = round(time.time() - t, 1)
    res[f"{name}_exit"] = code
    res[f"{name}_rss_mb"] = round(ru.ru_maxrss / (1 << 20 if platform.system() == "Darwin"
                                                  else 1 << 10))
    if timed_out:
        return "timeout"
    return "killed" if code in (-9, 137) else ("ok" if code == 0 else f"fail{code}")


def size(path):
    return os.path.getsize(path) if os.path.exists(path) else 0


def lean_setup(lean):
    """(environment with LEAN_PATH and PATH, plugin flags) for a direct `lean` call."""
    lp = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=lean,
                        stdout=subprocess.PIPE, text=True, check=True).stdout.strip()
    L = os.path.join(lean, ".lake")
    plugins = [f"--plugin={L}/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.{EXT}",
               f"--plugin={L}/build/lib/libCountCatcher_CountCatcherChecker.{EXT}"]
    return lp, plugins


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


def read_kv(path):
    d = {}
    if os.path.exists(path):
        with open(path) as f:
            for line in f:
                if "=" in line:
                    k, v = line.rstrip("\n").split("=", 1)
                    d[k] = v
    return d


def lemma(P, e):
    n = P["n"]
    if e["cells"] is None:
        return f"Latin.fibre_card_of_check (n := {n}) (r := {vec(e['rep'])})"
    return f"Latin.cell_card_of_check (n := {n}) (r := {vec(e['rep'])}) (t := {lst(e['cells'])})"


def leaf_thm(P, e):
    """The theorem of a leaf: PREFIX_fibreI for a whole fibre of class I (the listing's
    latin7_fibre0), PREFIX_LEAF for a part of a split fibre (latin8_c6_0025)."""
    if e["cells"] is None:
        return f"{P['prefix']}_fibre{e['class']}"
    return f"{P['prefix']}_{e['name']}"


def run_leaf(a, P, out, idx):
    e = P["leaves"][idx]
    name, thm = e["name"], leaf_thm(P, e)
    resd = os.path.join(out, "res")
    mod = os.path.realpath(a.mod or os.path.join(out, "mod"))
    os.makedirs(resd, exist_ok=True)
    os.makedirs(os.path.join(mod, P["pkg"]), exist_ok=True)
    rpath = os.path.join(resd, f"{name}.txt")
    if read_kv(rpath).get("status") == "proved":
        print(f"latin_cycles: leaf {idx} {name}: already proved")
        return True
    scratch = a.scratch or os.environ.get("SLURM_TMPDIR") or os.path.join(out, "work")
    work = os.path.join(os.path.realpath(scratch), f"{P['prefix']}_{name}")
    leafsrc = os.path.join(mod, P["pkg"], f"{name}.lean")
    rw = os.path.relpath(work, os.path.dirname(leafsrc))  # certificate paths relative to the module
    shutil.rmtree(work, ignore_errors=True)
    os.makedirs(work)
    lean = os.path.realpath(a.lean)
    lp, plugins = lean_setup(lean)
    env = dict(os.environ, PATH=os.path.realpath(a.tools) + os.pathsep + os.environ.get("PATH", ""))
    lenv = dict(env, LEAN_PATH=lp + os.pathsep + mod)
    res = {"leaf": name, "index": idx, "class": e["class"], "rep": tname(e["rep"]),
           "cells": "" if e["cells"] is None else tname(e["cells"]),
           "host": socket.gethostname(), "start": time.strftime("%Y-%m-%dT%H:%M:%S")}
    if "count_d4" in e:
        res["count_plan"] = e["count_d4"]

    def fin(status):
        res["status"] = status
        res["end"] = time.strftime("%Y-%m-%dT%H:%M:%S")
        res["peak_rss_mb"] = max([v for k, v in res.items() if k.endswith("_rss_mb")] or [0])
        with open(rpath + ".tmp", "w") as f:
            for k, v in res.items():
                f.write(f"{k}={v}\n")
        os.replace(rpath + ".tmp", rpath)
        if not a.keep_cert:
            shutil.rmtree(work, ignore_errors=True)
        print(f"latin_cycles: leaf {idx} {name}: {status}", flush=True)
        return status == "proved"

    # 1. the formula, exported from the Lean term
    src = os.path.join(work, "export.lean")
    with open(src, "w") as f:
        f.write("\n".join(HEADER) + f'\n#export_cnf via ({lemma(P, e)}) "{work}/in.cnf"\n')
    st = stage(res, "export", ["lean", *plugins, src], lean, a.to_lean,
               os.path.join(work, "export.out"), lenv)
    if st != "ok" or not os.path.exists(os.path.join(work, "in.cnf")):
        return fin(f"export_{st}")
    # 2. D4
    st = stage(res, "d4", ["d4", "in.cnf", "-dDNNF", "-out=in.nnf"], work, a.to_d4,
               os.path.join(work, "d4.log"), env)
    m = re.search(r"^s (\d+)", open(os.path.join(work, "d4.log")).read(), re.M)
    if st != "ok" or not m:
        return fin(f"d4_{st}")
    count = int(m.group(1))
    res["count_d4"] = count
    res["nnf_bytes"] = size(os.path.join(work, "in.nnf"))
    if "count_d4" in e and e["count_d4"] != count:
        return fin("count_mismatch_plan")
    # 3. certificate
    if count == 0:
        os.remove(os.path.join(work, "in.nnf"))
        strip_tautologies(os.path.join(work, "in.cnf"), os.path.join(work, "in_nt.cnf"))
        st = stage(res, "cadical", ["cadical", "-q", "--lrat", "--no-binary", "--no-factor",
                                    "in_nt.cnf", "unsat.lrat"], work, a.to_gen,
                   os.path.join(work, "cadical.log"), env)
        if res["cadical_exit"] != 20:
            return fin(f"cadical_{st}")
        res["lrat_bytes"] = size(os.path.join(work, "unsat.lrat"))
        files = f'"{rw}/unsat.lrat"'
        hint = ""
    else:
        st = stage(res, "gen", [*GEN, "in.cnf", "in.nnf", "cert.cpog"], work,
                   a.to_gen, os.path.join(work, "gen.log"), env)
        res["cpog_bytes"] = size(os.path.join(work, "cert.cpog"))
        os.remove(os.path.join(work, "in.nnf"))
        if st != "ok":
            return fin(f"gen_{st}")
        fl = ["--delete", "--keep", "--binary"] + ([] if a.no_inline else ["--inline"])
        res["c2l_flags"] = " ".join(fl)
        st = stage(res, "c2l", ["cpog2lrat", "in.cnf", "cert.cpog", "fwd", *fl], work,
                   a.to_gen, os.path.join(work, "c2l.log"), env)
        if not a.keep_cert:
            os.remove(os.path.join(work, "cert.cpog"))
        if st != "ok":
            return fin(f"c2l_{st}")
        for x in ("pog", "lrat", "keep"):
            res[f"{x}_bytes"] = size(os.path.join(work, f"fwd.{x}"))
        with open(os.path.join(work, "fwd.keep")) as f:
            mask = f.read()
        res["mask_kept"], res["mask_len"] = mask.count("1"), len(mask.strip())
        files = (f'"{rw}/fwd.pog" "{rw}/fwd.lrat" (keep := "{rw}/fwd.keep")')
        hint = f" (count := {count})"
    # 4. the leaf theorem, compiled to its own module
    src = leafsrc
    with open(src, "w") as f:
        f.write("\n".join(HEADER) + f"\ncount_models {thm} via ({lemma(P, e)}) {files}{hint}\n\n"
                f"#print axioms {thm}\n")
    olean = src[:-5] + ".olean"
    st = stage(res, "lean", ["lean", *plugins, "-R", mod, "-o", olean, src], lean, a.to_lean,
               os.path.join(resd, f"{name}.lean.out"), lenv)
    lo = open(os.path.join(resd, f"{name}.lean.out")).read()
    m = re.search(r"count_models \S+: (\d+) models", lo)
    res["count_lean"] = int(m.group(1)) if m else ""
    res["olean_bytes"] = size(olean)
    res["axioms"] = " ".join(re.findall(r"depends on axioms: \[([^\]]*)\]", lo)).replace("\n", " ")
    ok = st == "ok" and "error" not in lo and "depends on axioms" in lo and \
        res["count_lean"] == count
    return fin("proved" if ok else f"lean_{st}")


def leaf_counts(P, resd, put=None):
    """{leaf name: count} from OUT/res/<leaf>.txt; every leaf must say status=proved, and its
    count must equal the plan's expected count where one is given."""
    missing, bad, counts = [], [], {}
    for e in P["leaves"]:
        r = read_kv(os.path.join(resd, f"{e['name']}.txt"))
        if r.get("status") != "proved":
            missing.append(f"{e['index']}:{e['name']}({r.get('status', 'no result')})")
            continue
        c = int(r["count_d4"])
        if "count_d4" in e and e["count_d4"] != c or str(r.get("count_lean", c)) != str(c):
            bad.append(f"{e['index']}:{e['name']}(plan {e.get('count_d4')}, leaf {c}, "
                       f"Lean {r.get('count_lean')})")
        counts[e["name"]] = c
    if missing or bad:
        if put:
            put("status", "incomplete")
            put("missing", " ".join(missing))
            put("count_mismatch", " ".join(bad))
        sys.exit(f"latin_cycles: {len(missing)} leaves not proved, {len(bad)} with a count "
                 f"different from the plan: {' '.join((missing + bad)[:20])}")
    return counts


def totals(P, counts):
    classes = P["classes"]
    fib = {i: sum(counts[e["name"]] for e in P["leaves"] if e["class"] == i)
           for i in range(len(classes))}
    return fib, sum(fib[i] * c["size"] for i, c in enumerate(classes))


def assembly(P, counts):
    """The theorems after the leaves: a fibre theorem per split class (from its parts by
    Latin.fibre_card_eq_of_cells), PREFIX_reduced (Latin.card_eq_of_classes), PREFIX_all
    (Latin.card_latin_eq), and #print axioms of the last two. The leaf theorems are those of
    leaf_thm (count_models lines of the same file, or imported leaf modules)."""
    n, k, Pre, classes = P["n"], P["k"], P["prefix"], P["classes"]
    fib, N = totals(P, counts)
    T, fibre_thm = [], {}
    for i, c in enumerate(classes):
        ls = [e for e in P["leaves"] if e["class"] == i]
        q = c["rep"]
        if ls[0]["cells"] is None:
            fibre_thm[i] = leaf_thm(P, ls[0])
            continue
        name = f"{Pre}_fibre{i}"
        fibre_thm[i] = name
        entries = [f"({lst(e['cells'])}, {counts[e['name']]})" for e in ls]
        T += [f"/-- The fibre of the representative {tname(q)} (cycle type {c['type']}), from "
              f"{len(ls)} parts by the cells (2, 1..{k}). -/",
              f"theorem {name} :",
              f"    Nat.card {{L : Fin {n} → Fin {n} → Fin {n} // IsReducedLatin L ∧ L 1 = "
              f"{vec(q)}}} = {fib[i]} :=",
              f"  Latin.fibre_card_eq_of_cells (by norm_num) {vec(q)} {k} (by norm_num) {fib[i]}",
              "    [" + ",\n     ".join(entries) + "]",
              f"    ({chain([leaf_thm(P, e) for e in ls])})",
              "    (by decide +kernel)",
              "    (by decide +kernel)", ""]
    return T + reduced_all(P, fib, N, [fibre_thm[i] for i in range(len(classes))])


def reduced_all(P, fib, N, facts, binders=(), names=()):
    """PREFIX_reduced and PREFIX_all from the fibre facts; binders: hypotheses of both theorems,
    passed on by name (names) from PREFIX_all to PREFIX_reduced."""
    n, Pre, classes = P["n"], P["prefix"], P["classes"]
    reps = [f"({vec(c['rep'])}, {fib[i]})" for i, c in enumerate(classes)]
    alist = [f"({lst(p)}, {lst(s)}, {i})" for p, s, i in P["assign"]]
    hyp = [f"    {b}" for b in binders]
    use = "".join(f" {x}" for x in names)
    return [f"/-- The number of reduced Latin squares of order {n}, from {len(classes)} certified",
            "    fibre counts, one per cycle type of the second row (`Latin.card_eq_of_classes`). -/",
            f"theorem {Pre}_reduced" + ("" if hyp else " :"), *hyp[:-1],
            *([hyp[-1] + " :"] if hyp else []),
            f"    Nat.card {{L : Fin {n} → Fin {n} → Fin {n} // IsReducedLatin L}} = {N} :=",
            f"  Latin.card_eq_of_classes (by norm_num) {N}",
            "    [" + ",\n     ".join(reps) + "]",
            f"    ({chain(facts)})",
            "    [" + ",\n     ".join(alist) + "]",
            "    (by decide +kernel)",
            "    (by decide +kernel)", "",
            f"/-- All Latin squares of order {n}: `{n}! · {n - 1}!` times the reduced ones. -/",
            f"theorem {Pre}_all" + ("" if hyp else " :"), *hyp[:-1],
            *([hyp[-1] + " :"] if hyp else []),
            f"    Nat.card {{L : Fin {n} → Fin {n} → Fin {n} // IsLatin L}} = "
            f"{math.factorial(n) * math.factorial(n - 1) * N} := by",
            f"  rw [Latin.card_latin_eq, {Pre}_reduced{use}]; decide",
            "", f"#print axioms {Pre}_reduced", f"#print axioms {Pre}_all"]


def check_file(a, thy, out_txt, extra_path, put, Pre):
    """Lean on the theorem file thy (plugins loaded, LEAN_PATH plus extra_path); record the
    axioms of PREFIX_reduced and PREFIX_all; return whether PREFIX_all is proved."""
    lean = os.path.realpath(a.lean)
    lp, plugins = lean_setup(lean)
    res = {}
    st = stage(res, "asm", ["lean", *plugins, thy], lean, a.to_lean, out_txt,
               dict(os.environ, LEAN_PATH=lp + (os.pathsep + extra_path if extra_path else "")))
    for key, v in res.items():
        put(key, v)
    txt = open(out_txt).read()
    proved = st == "ok" and "error" not in txt and f"'{Pre}_all' depends on axioms" in txt
    for t in ("reduced", "all"):
        m = re.search(rf"'{Pre}_{t}' depends on axioms: \[(.*?)\]", txt, re.S)
        if m:
            ax = [x.strip() for x in m.group(1).split(",")]
            sfx = "" if t == "reduced" else "_all"  # the keys without suffix as before
            put(f"axioms_total{sfx}", len(ax))
            put(f"axioms_native{sfx}", sum(1 for x in ax if "native" in x))
            put(f"axioms_sorry{sfx}", sum(1 for x in ax if "sorry" in x))
    put("status", "proved" if proved else f"lean_{st}")
    return proved


def assemble(a, P, out):
    n, Pre = P["n"], P["prefix"]
    resd = os.path.join(out, "res")
    mod = os.path.realpath(a.mod or os.path.join(out, "mod"))
    kv = open(os.path.join(out, "assemble.txt"), "w")

    def put(key, v):
        kv.write(f"{key}={v}\n")
        kv.flush()

    counts = leaf_counts(P, resd, put)
    fib, N = totals(P, counts)
    put("count", N)
    for i, c in enumerate(P["classes"]):
        put(f"class_{i}", f"type={','.join(map(str, c['type']))} size={c['size']} fibre={fib[i]}")
    if n in REDUCED and N != REDUCED[n]:
        print(f"latin_cycles: count {N} differs from the known {REDUCED[n]}", flush=True)
    T = [*HEADER[:2], *(f"import {P['pkg']}.{e['name']}" for e in P["leaves"]), "",
         "open CountCatcher CountCatcher.Latin", "", "set_option maxRecDepth 100000",
         "set_option maxHeartbeats 0", "", *assembly(P, counts)]
    thy = os.path.join(mod, "T.lean")
    with open(thy, "w") as f:
        f.write("\n".join(T) + "\n")
    shutil.copy(thy, os.path.join(out, "T.lean"))
    proved = check_file(a, thy, os.path.join(out, "lean.out"), mod, put, Pre)
    kv.close()
    print(f"latin_cycles: assemble: {'proved' if proved else 'FAILED, see ' + out + '/lean.out'}"
          f" count {N}")
    return proved


def single(a, P, out):
    """--single: one theorem file OUT/PREFIX.lean as in the paper's listing. Each fibre is
    certified by the count-catcher driver (scripts/count_catcher.py NAME --via LEMMA, NAME the
    leaf theorem, e.g. latin7_fibre0) in OUT/cI; its count_models line is copied into the file
    with the paths prefixed by cI/, then PREFIX_reduced and PREFIX_all are appended and the file
    is checked. The certificates stay in OUT/cI (the file refers to them)."""
    n, Pre = P["n"], P["prefix"]
    if P["k"]:
        sys.exit("latin_cycles: --single certifies whole fibres only (--k 0)")
    for opt, d in (("--lean", os.path.join(REPO, "lean")), ("--tools", os.path.join(REPO, "tools", "bin"))):
        if os.path.realpath(getattr(a, opt[2:])) != os.path.realpath(d):
            sys.exit(f"latin_cycles: --single runs scripts/count_catcher.py, which uses {d}; "
                     f"drop {opt}")
    kv = open(os.path.join(out, "assemble.txt"), "w")

    def put(key, v):
        kv.write(f"{key}={v}\n")
        kv.flush()

    resd = os.path.join(out, "res")
    os.makedirs(resd, exist_ok=True)
    lines, counts = [], {}
    for e in P["leaves"]:
        thm, sub = leaf_thm(P, e), f"c{e['class']}"
        d = os.path.join(out, sub)
        shutil.rmtree(d, ignore_errors=True)
        cmd = [sys.executable, os.path.join(REPO, "scripts", "count_catcher.py"), thm,
               "--via", lemma(P, e), "--dir", d]
        print(f"latin_cycles: count-catcher {thm} --via '{lemma(P, e)}' --dir {d}", flush=True)
        res = {"leaf": e["name"], "theorem": thm, "dir": sub}
        st = stage(res, "cc", cmd, out, a.to_gen, os.path.join(resd, f"{e['name']}.cc.log"))
        src = os.path.join(d, f"{thm}.lean")
        txt = open(src).read() if os.path.exists(src) else ""
        m = re.search(rf"^count_models {thm} via \((.*)\) (\".*)$", txt, re.M)
        if st != "ok" or not m:
            put("status", f"count_catcher_{st}")
            sys.exit(f"latin_cycles: count-catcher failed for {thm} (log res/{e['name']}.cc.log)")
        files = re.sub(r'"([^"]+)"', lambda x: f'"{sub}/{x.group(1)}"', m.group(2))
        c = re.search(r"\(count := (\d+)\)", files)
        counts[e["name"]] = int(c.group(1))
        res.update(count_d4=c.group(1), status="proved")  # proved once the file is checked
        lines += [f"count_models {thm}", f"  via ({m.group(1)})", f"  {files}"]
        put(f"leaf_{e['name']}", f"theorem={thm} count={c.group(1)} keep={'keep :=' in files} "
            f"cc_s={res['cc_s']}")
    fib, N = totals(P, counts)
    put("count", N)
    for i, c in enumerate(P["classes"]):
        put(f"class_{i}", f"type={','.join(map(str, c['type']))} size={c['size']} fibre={fib[i]}")
    T = ["import CountCatcher", "", "open CountCatcher CountCatcher.Latin", "",
         "set_option maxRecDepth 100000", "", *lines, "", *assembly(P, counts)]
    thy = os.path.realpath(os.path.join(out, f"{Pre}.lean"))
    with open(thy, "w") as f:
        f.write("\n".join(T) + "\n")
    proved = check_file(a, thy, os.path.join(out, "lean.out"), "", put, Pre)
    kv.close()
    print(f"latin_cycles: single file {thy}: {'proved' if proved else 'FAILED, see lean.out'}"
          f" count {N}")
    return proved


def assemble_hyp(a, P, resd, thy):
    """--assemble-hyp: PREFIX_all with the leaf counts as hypotheses, one per fibre class: the
    hypothesis hT of Latin.fibre_card_eq_of_cells over the list of the class's parts and counts
    (from OUT/res/<leaf>.txt). Checks coverage (the parts are exactly Latin.thirdRows), the
    sums and the class assignment by decide +kernel without any certificate; written to thy
    (with thy minus .lean plus .txt, key=value, and .out, Lean's output) and checked."""
    n, k, Pre, classes = P["n"], P["k"], P["prefix"], P["classes"]
    if not k:
        sys.exit("latin_cycles: --assemble-hyp needs a split plan (--k > 0)")
    thy = os.path.realpath(thy)
    base = os.path.splitext(thy)[0]
    kv = open(base + ".txt", "w")

    def put(key, v):
        kv.write(f"{key}={v}\n")
        kv.flush()

    counts = leaf_counts(P, resd, put)
    fib, N = totals(P, counts)
    put("count", N)
    put("leaves", len(P["leaves"]))
    hyp = f"{Pre}_leaves"
    T = ["import CountCatcherMath.Families.LatinCycle", "",
         "/-! Latin squares of order " + f"{n} from the counts of the {len(P['leaves'])} leaf "
         "certificates as hypotheses, one per fibre class.",
         "", f"Each fibre (reduced squares with a given second row) is split by the cells "
         f"(2, 1..{k}) of the third",
         "row; a leaf is one filling `t` of these cells, and its theorem (`count_models` with",
         "`Latin.cell_card_of_check`, e.g. " + f"`{leaf_thm(P, P['leaves'][0])}`) states that `Latin.cellCnf {n} r t` has",
         "the leaf's count of models. The hypothesis of a class is the conjunction of these "
         "statements over",
         "the list of its parts. The proofs check, by `decide +kernel` and without "
         "certificates, that the parts",
         "are exactly the admissible fillings (`Latin.thirdRows`), that the counts add up, "
         "and that every admissible",
         "second row is carried onto its class representative; `#print axioms` lists the three "
         "standard axioms only.", "",
         "Written by `scripts/showcase/latin_cycles.py --plan PLAN --assemble-hyp` from the plan "
         f"and the leaf results of the order-{P['n']} run ({len(P['leaves'])} leaves). -/", "",
         "open CountCatcher CountCatcher.Latin", "", "set_option maxRecDepth 100000",
         "set_option maxHeartbeats 0", "",
         f"/-- The statement of the leaf theorems of the fibre of `r`: for every part `(t, N)` of "
         f"`T`, the formula",
         f"    `cellCnf {n} r t` has `N` models (the conclusion of `Latin.cell_card_of_check`). -/",
         f"def {hyp} (r : Fin {n} → Fin {n}) (T : List (List ℕ × ℕ)) : Prop :=",
         f"  ∀ p ∈ T, Fintype.card {{a : Fin ({n} * {n} * {n}) → Bool // (cellCnf {n} r p.1).eval "
         f"(ext a) = true}} = p.2", ""]
    hs, facts = [], []
    for i, c in enumerate(classes):
        ls = [e for e in P["leaves"] if e["class"] == i]
        q = c["rep"]
        if ls[0]["cells"] is None:
            sys.exit("latin_cycles: --assemble-hyp needs every class split (no --split)")
        entries = [f"({lst(e['cells'])}, {counts[e['name']]})" for e in ls]
        T += [f"/-- The {len(ls)} parts of the fibre of {tname(q)} (cycle type {c['type']}): "
              f"the cells (2, 1..{k}) and the",
              f"    leaf count, leaves {ls[0]['name']} to {ls[-1]['name']}. -/",
              f"def {Pre}_T{i} : List (List ℕ × ℕ) :=",
              "  [" + ",\n   ".join(entries) + "]", "",
              f"theorem {Pre}_fibre{i} (h : {hyp} {vec(q)} {Pre}_T{i}) :",
              f"    Nat.card {{L : Fin {n} → Fin {n} → Fin {n} // IsReducedLatin L ∧ L 1 = "
              f"{vec(q)}}} = {fib[i]} :=",
              f"  Latin.fibre_card_eq_of_cells (by norm_num) {vec(q)} {k} (by norm_num) {fib[i]}",
              f"    {Pre}_T{i} h (by decide +kernel) (by decide +kernel)", ""]
        hs.append(f"(h{i} : {hyp} {vec(q)} {Pre}_T{i})")
        facts.append(f"{Pre}_fibre{i} h{i}")
    T += reduced_all(P, fib, N, facts, hs, [f"h{i}" for i in range(len(classes))])
    with open(thy, "w") as f:
        f.write("\n".join(T) + "\n")
    proved = check_file(a, thy, base + ".out", "", put, Pre)
    kv.close()
    print(f"latin_cycles: assemble-hyp {thy}: {'proved' if proved else 'FAILED, see ' + base + '.out'}"
          f" count {N}")
    return proved


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--n", type=int)
    ap.add_argument("--k", type=int, default=0, help="split fibres by the cells (2, 1..k)")
    ap.add_argument("--split", help="cycle types to split, e.g. '7;5,2' (default: all)")
    ap.add_argument("--out", help="output directory (plan, results, modules); with --plan: the "
                    "directory of the results (default: the plan's directory)")
    ap.add_argument("--plan", help="plan.json for --leaf and --assemble (OUT = its directory)")
    ap.add_argument("--plan-only", action="store_true")
    ap.add_argument("--leaf", type=int, help="certify and check leaf I of the plan")
    ap.add_argument("--assemble", action="store_true")
    ap.add_argument("--single", action="store_true",
                    help="one theorem file OUT/PREFIX.lean, fibres by the count-catcher driver")
    ap.add_argument("--assemble-hyp", action="store_true",
                    help="PREFIX_all with the leaf counts of OUT/res as hypotheses")
    ap.add_argument("--hyp-out", help="theorem file of --assemble-hyp (default OUT/PREFIX_all.lean)")
    ap.add_argument("--pilot-d4", help="D4 pilot table (name, count, nnf_bytes) for --plan-only")
    ap.add_argument("--tier-mb", type=int, default=150, help="memory tier boundary (.nnf MB)")
    ap.add_argument("--scratch", help="certificate directory (default $SLURM_TMPDIR, else OUT/work)")
    ap.add_argument("--inline", action="store_true", help="accepted for compatibility (inlining is the default)")
    ap.add_argument("--no-inline", action="store_true", help="do not pass --inline to cpog2lrat")
    ap.add_argument("--keep-cert", action="store_true")
    ap.add_argument("--mod", help="directory of the leaf modules (default OUT/mod); a leaf's "
                    ".olean holds its POG text and keep mask, about the size of its .nnf")
    ap.add_argument("--lean", default=os.path.join(REPO, "lean"))
    ap.add_argument("--tools", default=os.path.join(REPO, "tools", "bin"))
    ap.add_argument("--to-d4", type=int, default=0)
    ap.add_argument("--to-gen", type=int, default=0)
    ap.add_argument("--to-lean", type=int, default=0)
    a = ap.parse_args()
    if a.leaf is not None or a.assemble or a.assemble_hyp:
        if not (a.plan or a.out):
            sys.exit("latin_cycles: --leaf, --assemble and --assemble-hyp need --plan (or --out)")
        plan_path = a.plan or os.path.join(a.out, "plan.json")
        out = os.path.abspath(a.out if a.plan and a.out else os.path.dirname(os.path.abspath(plan_path)))
        os.makedirs(out, exist_ok=True)
        P = json.load(open(plan_path))
        if a.leaf is not None:
            ok = run_leaf(a, P, out, a.leaf)
        elif a.assemble_hyp:  # leaf results next to the plan, the file in OUT (or --hyp-out)
            ok = assemble_hyp(a, P, os.path.join(os.path.dirname(os.path.abspath(plan_path)), "res"),
                              a.hyp_out or os.path.join(out, f"{P['prefix']}_all.lean"))
        else:
            ok = assemble(a, P, out)
        sys.exit(0 if ok else 1)
    if a.n is None:
        sys.exit("latin_cycles: --n is required for planning")
    out = os.path.abspath(a.out or os.path.join("latin", f"latin{a.n}"))
    os.makedirs(out, exist_ok=True)
    P = write_plan(a, out)
    if a.plan_only:
        return
    if a.single:
        sys.exit(0 if single(a, P, out) else 1)
    t0 = time.time()
    failed = [e["index"] for e in P["leaves"] if not run_leaf(a, P, out, e["index"])]
    print(f"latin_cycles: {len(P['leaves'])} leaves in {time.time() - t0:.1f} s, "
          f"{len(failed)} failed", flush=True)
    if failed:
        sys.exit(f"latin_cycles: failed leaves {failed}")
    sys.exit(0 if assemble(a, P, out) else 1)


if __name__ == "__main__":
    main()

"""Exhaustive and random differential tests for the mccert pipeline (contract_audit.md, part 3).

Every formula goes through D4 (-dDNNF), cpog-gen, the native translator cpog2lrat, and is
written as a record to a bundle for the Lean driver `mccert-audit` (AuditMain.lean), which
checks it with `checkAll` and the streamed route. The expected count of every record is an
independent bit-parallel brute-force count (Lean semantics: variables above the header count
are false). Certificates that the translator accepts are also mutated (POG, LRAT, CPOG and
formula level); every mutant goes to the same bundle with the brute-force count of the formula
it is checked against, so an accepted mutant with a wrong count is flagged WRONG by the driver.

Formula sets (deterministic; a shard takes the indices i with i % NSHARDS == SHARD):
  E0..E3  all multisets of clauses over V = 0..3 variables (clause = set of literals of width
          at most min(V,3), tautologies and the empty clause included): E0 size <= 2,
          E1 size <= 6, E2 size <= 6, E3 size <= 4; E3 with index % 8 == 0 is repeated
          with header V = 4 (unused variable), set E3u (E3u:j is E3:8j)
  R       random: V 4..8, header V + {0,1,2}, m 0..4V, widths 0..4, tautologies, repeated
          literals, duplicate clauses
  RB      random, m 64..130 (two or three 63-clause batches in part C), V 10..13, widths 3..5

Outputs in OUTDIR: bundle (records), tools.tsv (one line per formula and per CPOG mutant:
toolchain outcome), pydiff.tsv (sampled comparison with scripts/cpog2lrat.py).

Usage: python3 difftest.py SET SHARD NSHARDS OUTDIR --tools DIR [--count N] [--mut K]
       [--seed S] [--py SCRIPT] [--pysample P] [--delsample P]
"""

import argparse
import itertools
import os
import random
import shutil
import subprocess
import sys
import time

# ---------------------------------------------------------------- formulas


def clause_types(V, maxw):
    lits = [l for v in range(1, V + 1) for l in (v, -v)]
    out = []
    for w in range(0, maxw + 1):
        for c in itertools.combinations(lits, w):
            out.append(list(c))
    return out


def multisets(types, maxsize):
    for k in range(maxsize + 1):
        for combo in itertools.combinations_with_replacement(range(len(types)), k):
            yield [list(types[i]) for i in combo]


def exhaustive(set_name):
    """Yield (name, header V, clauses)."""
    spec = {"E0": (0, 0, 2), "E1": (1, 2, 6), "E2": (2, 2, 6), "E3": (3, 3, 4), "E3u": (3, 3, 4)}
    V, maxw, maxs = spec[set_name]
    types = clause_types(V, maxw)
    for i, cls in enumerate(multisets(types, maxs)):
        if set_name == "E3u":
            if i % 8:
                continue
            yield f"{set_name}:{i // 8}", V + 1, cls  # E3u:j is E3:8j with header 4
        else:
            yield f"{set_name}:{i}", V, cls


def random_formula(rng, big):
    if big:
        V = rng.randint(10, 13)
        H = V
        m = rng.randint(64, 130)
        widths = [3, 4, 5]
        wp = [0.1, 0.4, 0.5]
    else:
        V = rng.randint(4, 8)
        H = V + rng.choices([0, 1, 2], [0.7, 0.2, 0.1])[0]
        m = rng.randint(0, 4 * V)
        widths = [0, 1, 2, 3, 4]
        wp = [0.005, 0.1, 0.3, 0.45, 0.145]
    cls = []
    for _ in range(m):
        if cls and rng.random() < 0.05:
            cls.append(list(rng.choice(cls)))  # duplicate clause
            continue
        w = min(rng.choices(widths, wp)[0], V)
        vs = rng.sample(range(1, V + 1), w)
        c = [v if rng.random() < 0.5 else -v for v in vs]
        if c and rng.random() < 0.04:
            c.append(-c[0])  # tautology
        if c and rng.random() < 0.04:
            c.append(c[-1])  # repeated literal
        rng.shuffle(c)
        cls.append(c)
    return H, cls


def formulas(set_name, count, seed):
    if set_name.startswith("E"):
        yield from exhaustive(set_name)
    else:
        rng = random.Random(f"{set_name}-{seed}")
        for i in range(count):
            H, cls = random_formula(rng, set_name == "RB")
            yield f"{set_name}:{i}", H, cls


def cnf_text(V, cls):
    return f"p cnf {V} {len(cls)}\n" + "".join(" ".join(map(str, c + [0])) + "\n" for c in cls)


def bf_count(V, cls):
    """Bit-parallel model count over 2^V assignments; variables above V are false."""
    N = 1 << V
    full = (1 << N) - 1
    masks = {}
    for i in range(V):
        half = 1 << i
        block = ((1 << half) - 1) << half
        masks[i + 1] = block * (full // ((1 << (2 * half)) - 1))
    acc = full
    for c in cls:
        cm = 0
        for l in c:
            v = abs(l)
            mv = masks.get(v, 0)
            cm |= mv if l > 0 else (full & ~mv)
        acc &= cm
        if not acc:
            break
    return bin(acc).count("1")


# ---------------------------------------------------------------- tools


def run(cmd, out=None, timeout=20, env=None, cwd=None):
    """Run a tool. cwd must be private to the task: cpog-gen writes its SAT-solver files
    reduction-N.cnf and reduction-N.lrat into the working directory, so parallel cpog-gen
    runs in one directory read each other's proofs (first run, 2026-09-30)."""
    try:
        if out:
            with open(out, "w") as f:
                return subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, timeout=timeout, env=env, cwd=cwd).returncode
        return subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=timeout, env=env, cwd=cwd).returncode
    except subprocess.TimeoutExpired:
        return "timeout"


def last_line(path):
    try:
        with open(path, errors="replace") as f:
            lines = [l.strip() for l in f if l.strip()]
        return lines[-1] if lines else ""
    except OSError:
        return ""


def msg_class(msg):
    """Short class of a translator or cpog-gen message."""
    for key in ("no root unit", "no root declaration", "C4:", "C2:", "unsupported step",
                "cite no earlier", "Traceback", "panicked", "error"):
        if key in msg:
            return key.rstrip(":").replace(" ", "_")
    return msg[:40].replace(" ", "_").replace("\t", "_") or "none"


def gen_class(path):
    try:
        text = open(path, errors="replace").read()
    except OSError:
        return "nolog"
    for key, cls in (("Compiled formula unsatisfiable", "unsat"), ("Reduced CNF contains empty clause", "empty_clause"),
                     ("OVERCOUNT", "overcount"), ("Failed to justify", "undercount"),
                     ("Error reading D4", "nnf_read"), ("rror", "error")):
        if key in text:
            return cls
    return "other"


# ---------------------------------------------------------------- mutations


def parse_pog(text):
    head, root, nodes = [], None, []
    for line in text.splitlines():
        t = line.split()
        if not t:
            continue
        if t[0] == "V":
            head = t
        elif t[0] == "r":
            root = int(t[1])
        elif t[0] == "p":
            nodes.append(["p", [int(x) for x in t[1:-1]], []])
        elif t[0] == "s":
            nodes.append(["s", [int(t[1]), int(t[2])], t[3:-1]])
    return head, root, nodes


def write_pog(head, root, nodes):
    out = [" ".join(head)] + ([f"r {root}"] if root is not None else [])
    for k, args, hints in nodes:
        if k == "p":
            out.append("p " + " ".join(map(str, args)) + (" " if args else " ") + "0")
        else:
            out.append(f"s {args[0]} {args[1]} " + " ".join(hints) + (" " if hints else "") + "0")
    return "\n".join(out) + "\n"


def rand_lit(rng, below):
    v = rng.randint(1, max(1, below))
    return v if rng.random() < 0.5 else -v


def pog_shape(text):
    """Shape of a translated POG: node, sum and product counts, negated edges into internal
    nodes, negated root node, literal root, empty and one-argument products."""
    head, root, nodes = parse_pog(text)
    V = int(head[1])
    negint = sum(1 for _, args, _ in nodes for x in args if x < 0 and -x > V)
    sums = sum(1 for k, _, _ in nodes if k == "s")
    empty = sum(1 for k, a, _ in nodes if k == "p" and not a)
    single = sum(1 for k, a, _ in nodes if k == "p" and len(a) == 1)
    r = root or 0
    return (f"nodes={len(nodes)} sums={sums} negint={negint} rootneg={int(r < 0 and -r > V)} "
            f"rootlit={int(abs(r) <= V)} emptyp={empty} singlep={single}")


def mutate_pog(rng, text, kind):
    head, root, nodes = parse_pog(text)
    V = int(head[1])
    nodes = [[k, list(a), list(h)] for k, a, h in nodes]
    idx = [i for i, n in enumerate(nodes) if n[1]]
    if kind == "flip_arg" and idx:
        i = rng.choice(idx); j = rng.randrange(len(nodes[i][1])); nodes[i][1][j] *= -1
    elif kind == "change_arg" and idx:
        i = rng.choice(idx); j = rng.randrange(len(nodes[i][1]))
        nodes[i][1][j] = rand_lit(rng, V + i)
    elif kind == "drop_arg":
        ps = [i for i in idx if nodes[i][0] == "p"]
        if not ps:
            return None
        i = rng.choice(ps); del nodes[i][1][rng.randrange(len(nodes[i][1]))]
    elif kind == "add_arg" and nodes:
        ps = [i for i, n in enumerate(nodes) if n[0] == "p"]
        if not ps:
            return None
        i = rng.choice(ps); nodes[i][1].insert(rng.randrange(len(nodes[i][1]) + 1), rand_lit(rng, V + i))
    elif kind == "root_neg" and root is not None:
        root = -root
    elif kind == "root_change" and root is not None:
        root = rand_lit(rng, V + len(nodes))
    elif kind == "sum_hint":
        ss = [i for i, n in enumerate(nodes) if n[0] == "s"]
        if not ss:
            return None
        i = rng.choice(ss); h = nodes[i][2]
        if h and rng.random() < 0.5:
            del h[rng.randrange(len(h))]
        else:
            nd = rng.randrange(max(1, i)); k = rng.randrange(4)
            if h and rng.random() < 0.5:
                h[rng.randrange(len(h))] = f"{nd}:{k}"
            else:
                h.append(f"{nd}:{k}")
    elif kind == "kind_swap" and nodes:
        i = rng.randrange(len(nodes)); k, a, h = nodes[i]
        if k == "s":
            nodes[i] = ["p", a, []]
        elif len(a) == 2:
            nodes[i] = ["s", a, []]
        else:
            return None
    elif kind == "dup_node" and nodes:
        i = rng.randrange(len(nodes)); nodes.insert(i, [nodes[i][0], list(nodes[i][1]), list(nodes[i][2])])
    else:
        return None
    new = write_pog(head, root, nodes)
    return new if new != text else None


def mutate_lrat(rng, text, kind):
    lines = [l.split() for l in text.splitlines() if l.strip()]
    adds = [i for i, t in enumerate(lines) if len(t) > 1 and t[1] != "d"]
    if not adds:
        return None
    i = rng.choice(adds)
    t = lines[i]
    z = t.index("0", 1)
    lits, hints = t[1:z], t[z + 1 : -1]
    if kind == "drop_hint" and hints:
        del hints[rng.randrange(len(hints))]
    elif kind == "change_hint" and hints:
        hints[rng.randrange(len(hints))] = str(rng.randint(1, max(1, int(t[0]) - 1)))
    elif kind == "flip_lit" and lits:
        j = rng.randrange(len(lits)); lits[j] = str(-int(lits[j]))
    elif kind == "drop_lit" and lits:
        del lits[rng.randrange(len(lits))]
    elif kind == "add_lit":
        lits.append(str(rand_lit(rng, max(abs(int(x)) for x in lits) if lits else 3)))
    elif kind == "drop_line":
        del lines[i]
        return "".join(" ".join(x) + "\n" for x in lines)
    elif kind == "swap_lines" and len(adds) > 1:
        j = rng.choice([a for a in adds if a != i])
        lines[i], lines[j] = lines[j], lines[i]
        return "".join(" ".join(x) + "\n" for x in lines)
    else:
        return None
    lines[i] = [t[0]] + lits + ["0"] + hints + ["0"]
    new = "".join(" ".join(x) + "\n" for x in lines)
    return new if new != text else None


def mutate_cpog(rng, text, kind, V):
    lines = text.splitlines()
    decl = [i for i, l in enumerate(lines) if len(l.split()) > 2 and l.split()[1] in ("p", "s")]
    adds = [i for i, l in enumerate(lines) if len(l.split()) > 2 and l.split()[1] == "a"]
    if kind in ("decl_flip", "decl_change", "decl_drop") and decl:
        i = rng.choice(decl); t = lines[i].split()
        u = int(t[2])
        if t[1] == "p":
            args = t[3:-1]
            if not args:
                return None
            j = rng.randrange(len(args))
            if kind == "decl_flip":
                args[j] = str(-int(args[j]))
            elif kind == "decl_change":
                args[j] = str(rand_lit(rng, u - 1))
            else:
                del args[j]
            lines[i] = " ".join(t[:3] + args + ["0"])
        else:
            j = rng.choice([3, 4])
            if kind == "decl_flip":
                t[j] = str(-int(t[j]))
            elif kind == "decl_change":
                t[j] = str(rand_lit(rng, u - 1))
            else:
                hs = t[5:-1]
                if not hs:
                    return None
                del hs[rng.randrange(len(hs))]
                t = t[:5] + hs + ["0"]
            lines[i] = " ".join(t)
    elif kind in ("add_drop_hint", "add_change_hint", "add_flip_lit") and adds:
        i = rng.choice(adds); t = lines[i].split()
        z = t.index("0", 2)
        lits, hints = t[2:z], t[z + 1 : -1]
        if kind == "add_drop_hint" and hints:
            del hints[rng.randrange(len(hints))]
        elif kind == "add_change_hint" and hints:
            hints[rng.randrange(len(hints))] = str(rng.randint(1, max(1, int(t[0]) - 1)))
        elif kind == "add_flip_lit" and lits:
            j = rng.randrange(len(lits)); lits[j] = str(-int(lits[j]))
        else:
            return None
        lines[i] = " ".join(t[:2] + lits + ["0"] + hints + ["0"])
    elif kind == "root_change":
        rs = [i for i, l in enumerate(lines) if l.startswith("r ")]
        if not rs:
            return None
        r = int(lines[rs[0]].split()[1])
        lines[rs[0]] = f"r {-r if rng.random() < 0.5 else rand_lit(rng, V + len(decl))}"
    else:
        return None
    new = "\n".join(lines) + "\n"
    return new if new != text else None


def mutate_formula(rng, V, cls, kind):
    cls = [list(c) for c in cls]
    if kind == "drop_clause" and cls:
        del cls[rng.randrange(len(cls))]
    elif kind == "add_clause" and V:
        w = rng.randint(1, min(3, V))
        cls.append([v if rng.random() < 0.5 else -v for v in rng.sample(range(1, V + 1), w)])
    elif kind == "flip_lit":
        cs = [i for i, c in enumerate(cls) if c]
        if not cs:
            return None
        i = rng.choice(cs); j = rng.randrange(len(cls[i])); cls[i][j] *= -1
    elif kind == "drop_lit":
        cs = [i for i, c in enumerate(cls) if len(c) > 1]
        if not cs:
            return None
        i = rng.choice(cs); del cls[i][rng.randrange(len(cls[i]))]
    else:
        return None
    return cls


POG_KINDS = ["flip_arg", "change_arg", "drop_arg", "add_arg", "root_neg", "root_change",
             "sum_hint", "kind_swap", "dup_node"]
LRAT_KINDS = ["drop_hint", "change_hint", "flip_lit", "drop_lit", "add_lit", "drop_line", "swap_lines"]
CPOG_KINDS = ["decl_flip", "decl_change", "decl_drop", "add_drop_hint", "add_change_hint",
              "add_flip_lit", "root_change"]
F_KINDS = ["drop_clause", "add_clause", "flip_lit", "drop_lit"]


# ---------------------------------------------------------------- main


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("set"); ap.add_argument("shard", type=int); ap.add_argument("nshards", type=int)
    ap.add_argument("outdir")
    ap.add_argument("--tools", required=True)
    ap.add_argument("--count", type=int, default=0)
    ap.add_argument("--mut", type=int, default=1)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--py", default="")
    ap.add_argument("--pysample", type=float, default=0.0)
    ap.add_argument("--delsample", type=float, default=0.0)
    a = ap.parse_args()
    os.makedirs(a.outdir, exist_ok=True)
    w = os.path.join(a.outdir, "work")
    os.makedirs(w, exist_ok=True)
    env = dict(os.environ, PATH=a.tools + os.pathsep + os.environ.get("PATH", ""))
    d4, gen, c2l = (os.path.join(a.tools, x) for x in ("d4", "cpog-gen", "cpog2lrat"))
    rng = random.Random(f"mut-{a.set}-{a.shard}-{a.seed}")
    fb = open(os.path.join(a.outdir, "bundle"), "w")
    ft = open(os.path.join(a.outdir, "tools.tsv"), "w")
    fp = open(os.path.join(a.outdir, "pydiff.tsv"), "w")
    t0 = time.time()
    nform = 0

    def record(name, exp, cnf, pog, lrat):
        fb.write(f"@inst {name} {exp}\n@cnf\n{cnf}@pog\n{pog}@lrat\n{lrat}@end\n")

    def translate(cnfp, cpogp, out, flags=()):
        for ext in (".pog", ".lrat", ".cnf"):
            if os.path.exists(out + ext):
                os.remove(out + ext)
        e = run([c2l, cnfp, cpogp, out, *flags], out + ".log", env=env, cwd=w)
        if e == 0:
            return 0, open(out + ".pog").read(), open(out + ".lrat").read(), ""
        return e, None, None, msg_class(last_line(out + ".log"))

    def pycompare(name, cnfp, cpogp, e_nat, pog, lrat):
        if not a.py:
            return
        out = os.path.join(w, "py")
        for ext in (".pog", ".lrat", ".cnf"):
            if os.path.exists(out + ext):
                os.remove(out + ext)
        e = run([sys.executable, a.py, cnfp, cpogp, out], out + ".log", timeout=60, cwd=w)
        if e != e_nat:
            fp.write(f"{name}\tDIFF-exit\tnative={e_nat}\tpy={e}\n")
        elif e == 0:
            same = open(out + ".pog").read() == pog and open(out + ".lrat").read() == lrat
            fp.write(f"{name}\t{'same' if same else 'DIFF-output'}\n")
        else:
            fp.write(f"{name}\tsame-reject\t{msg_class(last_line(out + '.log'))}\n")

    for name, V, cls in formulas(a.set, a.count, a.seed):
        idx = int(name.split(":")[1])
        if idx % a.nshards != a.shard:
            continue
        nform += 1
        cnf = cnf_text(V, cls)
        N = bf_count(V, cls)
        cnfp = os.path.join(w, "in.cnf")
        open(cnfp, "w").write(cnf)
        for f in ("in.nnf", "cert.cpog"):
            if os.path.exists(os.path.join(w, f)):
                os.remove(os.path.join(w, f))
        e4 = run([d4, cnfp, "-dDNNF", f"-out={w}/in.nnf"], os.path.join(w, "d4.log"), env=env, cwd=w)
        cnt = "?"
        try:
            for l in open(os.path.join(w, "d4.log")):
                if l.startswith("s "):
                    cnt = l.split()[1]
                    break
        except OSError:
            pass
        eg = run([gen, cnfp, os.path.join(w, "in.nnf"), os.path.join(w, "cert.cpog")],
                 os.path.join(w, "gen.log"), env=env, cwd=w) if e4 == 0 else "-"
        genmsg = gen_class(os.path.join(w, "gen.log")) if eg not in (0, "-") else ""
        cpogp = os.path.join(w, "cert.cpog")
        ec, pog, lrat, cmsg = translate(cnfp, cpogp, os.path.join(w, "fwd")) if eg == 0 else ("-", None, None, "")
        shape = pog_shape(pog) if ec == 0 else ""
        ft.write(f"T\t{name}\tV={V}\tm={len(cls)}\tbf={N}\td4={e4}\td4count={cnt}\tgen={eg}\t{genmsg}\tc2l={ec}\t{cmsg}\t{shape}\n")
        if eg == 0 and rng.random() < a.pysample:
            pycompare(name, cnfp, cpogp, ec, pog, lrat)
        if ec != 0:
            continue
        record(name, N, cnf, pog, lrat)
        if rng.random() < a.delsample:
            e, p2, l2, _ = translate(cnfp, cpogp, os.path.join(w, "fwdd"), ("--delete",))
            if e == 0:
                record(name + "/delete", N, cnf, p2, l2)
        seen = set()
        for kind in POG_KINDS:
            for j in range(a.mut):
                p2 = mutate_pog(rng, pog, kind)
                if p2 and p2 not in seen:
                    seen.add(p2)
                    record(f"{name}/mp_{kind}#{j}", N, cnf, p2, lrat)
        for kind in LRAT_KINDS:
            for j in range(a.mut):
                l2 = mutate_lrat(rng, lrat, kind)
                if l2 and l2 not in seen:
                    seen.add(l2)
                    record(f"{name}/ml_{kind}#{j}", N, cnf, pog, l2)
        for kind in F_KINDS:
            for j in range(a.mut):
                c2 = mutate_formula(rng, V, cls, kind)
                if c2 is not None:
                    record(f"{name}/mf_{kind}#{j}", bf_count(V, c2), cnf_text(V, c2), pog, lrat)
        cpog = open(cpogp).read()
        for kind in CPOG_KINDS:
            for j in range(a.mut):
                c2 = mutate_cpog(rng, cpog, kind, V)
                if not c2:
                    continue
                mp = os.path.join(w, "mut.cpog")
                open(mp, "w").write(c2)
                e, p2, l2, m = translate(cnfp, mp, os.path.join(w, "fwdm"))
                mname = f"{name}/mc_{kind}#{j}"
                ft.write(f"M\t{mname}\tc2l={e}\t{m}\n")
                if rng.random() < a.pysample:
                    pycompare(mname, cnfp, mp, e, p2, l2)
                if e == 0:
                    record(mname, N, cnf, p2, l2)
    fb.close(); ft.close(); fp.close()
    shutil.rmtree(w, ignore_errors=True)
    print(f"difftest {a.set} shard {a.shard}/{a.nshards}: {nform} formulas, {time.time() - t0:.1f} s")


if __name__ == "__main__":
    main()

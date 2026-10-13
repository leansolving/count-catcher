"""Summarize the differential-test results (contract_audit.md, part 3).

Reads RESULTS/*/{info.txt,lean.out.gz,tools.tsv.gz,pydiff.tsv} as written by audit.sbatch and
prints: per set the toolchain outcomes of the base formulas (D4 against the brute-force count,
cpog-gen, translator), the Lean verdicts per record kind (base, delete, mutants) with the
rejecting stage, every flagged record (WRONG, BFDIFF, DIAGDIFF, STREAMDIFF, CDIFF), every
base certificate that the Lean checker rejects, and the translator comparison.

Usage: python3 summarize.py RESULTS
"""

import collections
import glob
import gzip
import os
import re
import sys


def kind_of(name):
    if "/" not in name:
        return "base"
    k = name.split("/", 1)[1]
    return re.sub(r"#\d+$", "", k)


def stage_class(st):
    st = re.sub(r"^stage=", "", st)
    st = re.sub(r"A-node\d+-", "A-", st)
    st = re.sub(r"C-clause\d+", "C-clause", st)
    st = re.sub(r"pog-V\d+", "pog-V", st)
    return st


def main():
    res = sys.argv[1]
    dirs = sorted(glob.glob(os.path.join(res, "*_*")))
    tools = collections.defaultdict(collections.Counter)  # set -> outcome counter
    shapes = collections.defaultdict(collections.Counter)  # set -> POG shape totals
    d4bad = []
    mtools = collections.defaultdict(collections.Counter)  # mutant kind -> translator outcome
    lean = collections.defaultdict(collections.Counter)  # (set, kind) -> (verdict, stage)
    lean_all = collections.defaultdict(collections.Counter)  # kind -> (verdict, stage)
    flagged = []
    base_rej = []
    py = collections.Counter()
    pydiff = []
    info = []
    nrec = 0
    for d in dirs:
        s = os.path.basename(d).rsplit("_", 1)[0]
        try:
            info.append((os.path.basename(d), open(os.path.join(d, "info.txt")).read()))
        except OSError:
            info.append((os.path.basename(d), "MISSING info.txt"))
        tp = os.path.join(d, "tools.tsv.gz")
        if os.path.exists(tp):
            for line in gzip.open(tp, "rt"):
                f = line.rstrip("\n").split("\t")
                if f[0] == "T":
                    kv = dict(x.split("=", 1) for x in f[2:] if "=" in x)
                    sat = "sat" if int(kv["bf"]) > 0 else "unsat"
                    d4ok = "d4=ok" if kv["d4"] == "0" and kv["d4count"] == kv["bf"] else f"d4=BAD({kv['d4']},{kv['d4count']})"
                    if d4ok != "d4=ok":
                        d4bad.append(line.strip())
                    gen = f"gen={kv['gen']}" + (f":{f[8]}" if f[8] else "")
                    c2l = f"c2l={kv['c2l']}" + (f":{f[10]}" if len(f) > 10 and f[10] else "")
                    tools[s][(sat, d4ok, gen, c2l)] += 1
                    if len(f) > 11 and f[11]:
                        sh = dict(x.split("=") for x in f[11].split())
                        agg = shapes[s]
                        agg["certs"] += 1
                        for k2 in ("nodes", "sums", "negint", "rootneg", "rootlit", "emptyp", "singlep"):
                            agg[k2] += int(sh[k2])
                        agg["maxnodes"] = max(agg["maxnodes"], int(sh["nodes"]))
                        if int(sh["emptyp"]):
                            agg["certs_with_emptyp"] += 1
                elif f[0] == "M":
                    k = kind_of(f[1])
                    mtools[k][f[2] + (":" + f[3] if len(f) > 3 and f[3] else "")] += 1
        lp = os.path.join(d, "lean.out.gz")
        if os.path.exists(lp):
            for line in gzip.open(lp, "rt"):
                if not line.startswith("R "):
                    continue
                t = line.split()
                nrec += 1
                name, verdict, stage = t[1], t[2], stage_class(t[3])
                flags = t[-1].split("=", 1)[1]
                k = kind_of(name)
                lean[(s, k)][(verdict, stage)] += 1
                lean_all[k][(verdict, stage)] += 1
                if flags != "OK":
                    flagged.append(line.strip())
                if k in ("base", "delete") and verdict != "ACCEPT":
                    base_rej.append(line.strip())
        pp = os.path.join(d, "pydiff.tsv")
        if os.path.exists(pp):
            for line in open(pp):
                f = line.rstrip("\n").split("\t")
                py[f[1]] += 1
                if f[1].startswith("DIFF"):
                    pydiff.append(line.strip())
    print(f"# result dirs: {len(dirs)}, Lean records: {nrec}")
    print("\n## Toolchain outcomes of the base formulas (sat/unsat by brute force)")
    for s in sorted(tools):
        tot = sum(tools[s].values())
        print(f"\n{s}: {tot} formulas")
        for key, n in tools[s].most_common():
            print(f"  {n:8d}  {' '.join(key)}")
    print("\n## Shapes of the translated base POGs (totals per set)")
    for s in sorted(shapes):
        print(f"  {s}: " + " ".join(f"{k}={v}" for k, v in sorted(shapes[s].items())))
    print(f"\nD4 count disagreements with brute force: {len(d4bad)}")
    for l in d4bad[:20]:
        print("  " + l)
    print("\n## Translator outcomes of CPOG-level mutants")
    for k in sorted(mtools):
        print(f"  {k}: " + ", ".join(f"{o} {n}" for o, n in mtools[k].most_common()))
    print("\n## Lean verdicts per record kind (all sets)")
    for k in sorted(lean_all):
        tot = sum(lean_all[k].values())
        acc = sum(n for (v, _), n in lean_all[k].items() if v == "ACCEPT")
        rest = ", ".join(f"{st} {n}" for (v, st), n in lean_all[k].most_common() if v != "ACCEPT")
        print(f"  {k}: {tot} records, {acc} accepted (all with the brute-force count unless flagged); rejected: {rest}")
    print("\n## Lean verdicts per set, base and delete records")
    for (s, k) in sorted(lean):
        if k in ("base", "delete"):
            print(f"  {s} {k}: " + ", ".join(f"{v}/{st} {n}" for (v, st), n in lean[(s, k)].most_common()))
    print(f"\n## Flagged records: {len(flagged)}")
    for l in flagged[:200]:
        print("  " + l)
    print(f"\n## Base or delete certificates rejected by the Lean checker: {len(base_rej)}")
    for l in base_rej[:100]:
        print("  " + l)
    print("\n## Native against Python translator (sampled)")
    print("  " + ", ".join(f"{k} {n}" for k, n in py.most_common()))
    for l in pydiff[:50]:
        print("  " + l)
    print("\n## Task info")
    for n, t in info:
        lines = [l for l in t.splitlines() if l.startswith(("host", "difftest_exit", "lean_exit", "SUMMARY", "difftest "))]
        print(f"  {n}: " + " | ".join(lines))


if __name__ == "__main__":
    main()

"""Summarize the differential-test results of the rerun (difftest_rerun.md).

Reads RESULTS/*/{info.txt,lean.out.gz,tools.tsv.gz} as written by audit_task.sh and prints:
per set the toolchain outcomes of the base formulas (D4 against the brute-force count, the
generator, both translations), the translator outcomes of the CPOG mutants, the Lean verdicts per
record kind with the rejecting stage (as a markdown table in the format of contract_audit.md 3.3),
the totals per route, every flagged record (WRONG, WRONGSTREAM, BFDIFF, DIAGDIFF, CDIFF,
CONTROL-FAIL), the informational STREAMDIFF and EMBDIFF records, the positive controls, every base
certificate that the Lean checker rejects, and the task times.

With --tsv FILE it also writes the per-kind table (kind, route, records, accepted, rejected stages
as STAGE:N,...) that scripts/paper_numbers.py reads for Table 11.

Usage: uv run --no-project python summarize.py RESULTS [--tsv FILE]
"""

import collections
import glob
import gzip
import os
import re
import sys

DESC = {
    "base": "text route, unmutated (`--delete --trim`)",
    "plain": "text route, unmutated, translator without flags (5% sample)",
    "default": "default route, unmutated (`--delete --keep --inline --binary`)",
    "mp_flip_arg": "POG: negate one node argument",
    "mp_change_arg": "POG: random earlier literal as argument",
    "mp_drop_arg": "POG: drop a product argument",
    "mp_add_arg": "POG: add a product argument",
    "mp_root_neg": "POG: negate the root",
    "mp_root_change": "POG: random root",
    "mp_sum_hint": "POG: drop, replace or add a sum hint",
    "mp_kind_swap": "POG: sum ↔ binary product",
    "mp_dup_node": "POG: duplicate a node line",
    "ml_drop_hint": "LRAT: drop a hint",
    "ml_change_hint": "LRAT: replace a hint",
    "ml_flip_lit": "LRAT: negate a literal of an addition",
    "ml_drop_lit": "LRAT: drop a literal of an addition",
    "ml_add_lit": "LRAT: add a literal to an addition",
    "ml_drop_line": "LRAT: drop an addition",
    "ml_swap_lines": "LRAT: swap two additions",
    "mf_drop_clause": "formula: drop a clause",
    "mf_add_clause": "formula: add a random clause",
    "mf_flip_lit": "formula: negate a literal",
    "mf_drop_lit": "formula: drop a literal",
    "mc_decl_flip": "CPOG: negate a declaration argument",
    "mc_decl_change": "CPOG: replace a declaration argument",
    "mc_decl_drop": "CPOG: drop a product argument or sum hint",
    "mc_add_drop_hint": "CPOG: drop a hint of an addition",
    "mc_add_change_hint": "CPOG: replace a hint of an addition",
    "mc_add_flip_lit": "CPOG: negate a literal of an addition",
    "mc_root_change": "CPOG: negate or replace the root",
    "kb_flip": "binary LRAT: flip one bit",
    "kb_trunc": "binary LRAT: truncate at a random byte",
    "kk_drop": "keep mask: drop one kept (cited) clause",
    "kk_add": "keep mask: keep one dropped clause",
}
for k in list(DESC):
    if k[:2] in ("mp", "ml", "mf", "mc"):
        DESC["k" + k[1:]] = DESC[k] + " (default route)"
TEXT_KINDS = ("base", "plain")
DEFAULT_ONLY = ("default",)


def kind_of(name):
    if "/" not in name:
        return "base"
    k = name.split("/", 1)[1]
    return re.sub(r"#\d+$", "", k)


def route_of(kind):
    if kind in TEXT_KINDS or kind[:2] in ("mp", "ml", "mf", "mc") or kind == "control_text":
        return "text"
    return "default"


def stage_class(st):
    st = re.sub(r"^stage=", "", st)
    st = re.sub(r"A-node\d+-", "A-", st)
    st = re.sub(r"C-clause\d+", "C-clause", st)
    st = re.sub(r"pog-V\d+", "pog-V", st)
    return {"B-check": "B", "A-args-not-earlier": "A-arg"}.get(st, st)


def order_key(kind):
    pre = ["base", "plain", "default"]
    if kind in pre:
        return (0, pre.index(kind), "")
    fam = ["mp", "ml", "mf", "mc", "kp", "kl", "kb", "kk", "kf", "kc"]
    return (1, fam.index(kind[:2]) if kind[:2] in fam else 99, kind)


STAGE_ORDER = ["cnf-wf", "pog-parse", "pog-V", "A-arg", "A-prod-overlap", "A-sum-hint-ref", "A-sum-rup",
               "A-root-range", "C-negation", "C-clause", "B-parse", "B"]


def fmt(n):
    return f"{n:,}"


def main():
    res = sys.argv[1]
    tsv = sys.argv[sys.argv.index("--tsv") + 1] if "--tsv" in sys.argv else None
    dirs = sorted(glob.glob(os.path.join(res, "*_*")))
    tools = collections.defaultdict(collections.Counter)
    d4bad, trdiff = [], []
    mtools = collections.defaultdict(collections.Counter)
    lean_all = collections.defaultdict(collections.Counter)  # kind -> (verdict, stage)
    lean_set = collections.defaultdict(collections.Counter)  # (set, kind) -> (verdict, stage)
    flagged, info_diff, controls, base_rej = [], collections.defaultdict(list), [], []
    panics = 0
    info = []
    nrec = 0
    tsums = collections.Counter()
    for d in dirs:
        s = os.path.basename(d).rsplit("_", 1)[0]
        try:
            txt = open(os.path.join(d, "info.txt")).read()
        except OSError:
            txt = "MISSING info.txt"
        info.append((os.path.basename(d), txt))
        for key in ("difftest_s", "lean_s", "lean_err_panics"):
            m = re.search(rf"{key}=(\d+)", txt)
            if m:
                tsums[key] += int(m.group(1))
        m = re.search(r"start=(\d+)", txt); m2 = re.search(r"end=(\d+)", txt)
        if m and m2:
            tsums["first_start"] = min(tsums["first_start"] or 10**12, int(m.group(1)))
            tsums["last_end"] = max(tsums["last_end"], int(m2.group(1)))
        tp = os.path.join(d, "tools.tsv.gz")
        if os.path.exists(tp):
            for line in gzip.open(tp, "rt"):
                f = line.rstrip("\n").split("\t")
                if f[0] == "T":
                    kv = dict(x.split("=", 1) for x in f[2:8] if "=" in x)
                    sat = "sat" if int(kv["bf"]) > 0 else "unsat"
                    d4ok = "d4=ok" if kv["d4"] == "0" and kv["d4count"] == kv["bf"] else f"d4=BAD({kv['d4']},{kv['d4count']})"
                    if d4ok != "d4=ok":
                        d4bad.append(line.strip())
                    gen = f"gen={kv['gen']}" + (f":{f[8]}" if f[8] else "")
                    c2l = f[9] + (f":{f[10]}" if f[10] else "")
                    c2lk = f[12].replace("c2lk", "c2lk") + (f":{f[13]}" if f[13] else "")
                    ex = dict(x.split("=", 1) for x in f[14].split()) if len(f) > 14 and f[14] else {}
                    extra = ""
                    if ex:
                        extra = f"pogsame={ex['pogsame']} rt={ex['rt']}"
                        if ex["pogsame"] != "1" or ex["rt"] != "1":
                            trdiff.append(line.strip())
                    if (f[9] == "c2l=0") != (f[12] == "c2lk=0"):
                        trdiff.append(line.strip())
                    tools[s][(sat, d4ok, gen, c2l, c2lk, extra)] += 1
                elif f[0] == "M":
                    k = kind_of(f[1])
                    mtools[k][f[2] + (":" + f[3] if len(f) > 3 and f[3] else "")] += 1
        lp = os.path.join(d, "lean.out.gz")
        if os.path.exists(lp):
            for line in gzip.open(lp, "rt"):
                if not line.startswith("R "):
                    continue
                t = line.split()
                name, verdict, stage = t[1], t[2], stage_class(t[3])
                flags = t[-1].split("=", 1)[1]
                k = kind_of(name)
                if k.startswith("control"):
                    controls.append((k, flags, line.strip()))
                    continue
                nrec += 1
                lean_all[k][(verdict, stage)] += 1
                lean_set[(s, k)][(verdict, stage)] += 1
                fl = set(flags.split(","))
                info_only = {"OK", "STREAMDIFF", "EMBDIFF"}
                if fl - info_only:
                    flagged.append(line.strip())
                for x in fl & {"STREAMDIFF", "EMBDIFF"}:
                    info_diff[(x, k, verdict)].append(line.strip())
                if k in ("base", "plain", "default") and verdict != "ACCEPT":
                    base_rej.append(line.strip())

    print(f"# result dirs: {len(dirs)}, Lean records (without controls): {nrec}, controls: {len(controls)}")
    print("\n## Toolchain outcomes of the base formulas (sat/unsat by brute force)")
    for s in sorted(tools):
        print(f"\n{s}: {sum(tools[s].values())} formulas")
        for key, n in tools[s].most_common():
            print(f"  {n:8d}  {' '.join(x for x in key if x)}")
    print(f"\nD4 count disagreements with brute force: {len(d4bad)}")
    for l in d4bad[:20]:
        print("  " + l)
    print(f"\nTranslations that differ (one route fails, POG differs, or binary round trip fails): {len(trdiff)}")
    for l in trdiff[:20]:
        print("  " + l)
    print("\n## Translator outcomes of CPOG-level mutants")
    for k in sorted(mtools, key=order_key):
        print(f"  {k}: " + ", ".join(f"{o} {n}" for o, n in mtools[k].most_common()))

    print("\n## Lean verdicts per record kind (all sets), contract_audit.md 3.3 format")
    print("\n| Kind | Mutation | Records | Accepted | Rejected by stage |\n|---|---|---:|---:|---|")
    rows = []
    for k in sorted(lean_all, key=order_key):
        c = lean_all[k]
        tot = sum(c.values())
        acc = sum(n for (v, _), n in c.items() if v == "ACCEPT")
        rej = collections.Counter()
        for (v, st), n in c.items():
            if v != "ACCEPT":
                rej[st] += n
        rest = ", ".join(f"{st} {fmt(n)}" for st, n in rej.most_common())
        print(f"| {k} | {DESC.get(k, k)} | {fmt(tot)} | {fmt(acc)} | {rest} |")
        rows.append((k, route_of(k), tot, acc, rej))
    if tsv:
        with open(tsv, "w") as f:
            f.write("kind\troute\trecords\taccepted\trejected\n")
            for k, r, tot, acc, rej in rows:
                f.write(f"{k}\t{r}\t{tot}\t{acc}\t" + ",".join(f"{st}:{n}" for st, n in sorted(rej.items())) + "\n")

    print("\n## Totals per route and in the order of the checker's conditions")
    for r in ("text", "default", "all"):
        sel = [x for x in rows if r == "all" or x[1] == r]
        tot = sum(x[2] for x in sel); acc = sum(x[3] for x in sel)
        unm = sum(x[3] for x in sel if x[0] in ("base", "plain", "default"))
        rej = collections.Counter()
        for x in sel:
            rej.update(x[4])
        stages = ", ".join(f"{st} {fmt(rej[st])}" for st in STAGE_ORDER if rej[st]) + \
            "".join(f", {st} {fmt(n)} (unordered)" for st, n in rej.items() if st not in STAGE_ORDER)
        print(f"  {r}: {fmt(tot)} records, {fmt(acc)} accepted ({fmt(unm)} unmutated, {fmt(acc - unm)} mutants); "
              f"rejected: {stages}")
    kb = {k: sum(c.values()) for k, c in lean_all.items()}
    ka = {k: sum(n for (v, _), n in c.items() if v == "ACCEPT") for k, c in lean_all.items()}
    print(f"\nTotals line (AUDIT_TOTALS format): {fmt(nrec)} Lean records, {fmt(sum(ka.values()))} accepted "
          f"({fmt(ka.get('base', 0) + ka.get('default', 0))} base, {fmt(ka.get('plain', 0))} delete, "
          f"{fmt(sum(v for k, v in ka.items() if k not in ('base', 'default', 'plain')))} mutants)")

    print("\n## Lean verdicts per set, unmutated records")
    for (s, k) in sorted(lean_set):
        if k in ("base", "plain", "default"):
            print(f"  {s} {k}: " + ", ".join(f"{v}/{st} {n}" for (v, st), n in lean_set[(s, k)].most_common()))
    print(f"\n## Flagged records (WRONG, WRONGSTREAM, BFDIFF, DIAGDIFF, CDIFF, ...): {len(flagged)}")
    for l in flagged[:200]:
        print("  " + l)
    print("\n## Informational differences (streamed against embedded part B)")
    for (x, k, v), ls in sorted(info_diff.items()):
        print(f"  {x} {k} verdict={v}: {len(ls)}; e.g. {ls[0]}")
    cc = collections.Counter((k, f) for k, f, _ in controls)
    print(f"\n## Positive controls: {len(controls)}: " + ", ".join(f"{k} {f} {n}" for (k, f), n in sorted(cc.items())))
    print(f"\n## Unmutated certificates rejected by the Lean checker: {len(base_rej)}")
    for l in base_rej[:100]:
        print("  " + l)
    print("\n## Times")
    print(f"  tool runs (difftest.py) {tsums['difftest_s']} s = {tsums['difftest_s'] / 3600:.2f} CPU-h; "
          f"Lean {tsums['lean_s']} s = {tsums['lean_s'] / 60:.1f} min; "
          f"wall {tsums['last_end'] - tsums['first_start']} s; "
          f"index-out-of-bounds messages of lrat-catcher {tsums['lean_err_panics']}")
    print("\n## Task info")
    for n, t in info:
        lines = [l for l in t.splitlines() if l.startswith(("host", "difftest_exit", "lean_exit", "SUMMARY", "difftest "))]
        print(f"  {n}: " + " | ".join(lines))


if __name__ == "__main__":
    main()

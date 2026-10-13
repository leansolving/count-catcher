"""Compare the reproduction results with the paper's values.

    python3 artifact/check.py [--stage NAME ...] [--item KEY ...] [--results FILE] [--expected FILE]
                              [--all-rows]

Reads artifact/out/results.tsv (written by artifact/reproduce.sh) and artifact/expected.tsv
(stage, item, expected, check, ref, source). Only the stages that appear in the results (or
those named with --stage) are checked. Per expected row:

  PASS     the item ran and its value meets the check
  FAIL     the item failed, was killed, is missing from a stage that ran, or its value does not
           meet the check
  SKIP     the item was skipped (reproduce.sh --skip-large)
  NOTRUN   the item was not selected: with --item (which reproduce.sh passes on), a missing
           row of an itemized stage (tests, showcases, validation, competition, streamed)
           whose item is not among the selected ones; it does not count as a failure
  INFO     a measured value without a pass criterion (for example a time ratio of one instance)

Checks: exact (the strings are equal), int (equal as integers; thousands separators ignored),
range LO HI (LO <= value <= HI), info. Prints one line per row and a summary per stage (wall
time summed over the items, the largest peak memory); exits 1 if any row FAILs, else 0.
artifact/out/results.tsv accumulates over invocations of reproduce.sh (a rerun replaces the
rows of what it reruns); the table covers the stages named with --stage, by default all
stages in the results.
Standard library only.
"""

import argparse
import sys
from pathlib import Path

ART = Path(__file__).resolve().parent
ITEMIZED = {"tests", "showcases", "validation", "competition", "streamed"}  # as in reproduce.py


def read_tsv(path):
    lines = Path(path).read_text().splitlines()
    hdr = lines[0].split("\t")
    return [dict(zip(hdr, l.split("\t"))) for l in lines[1:] if l.strip() and not l.startswith("#")]


def num(s):
    try:
        return float(s)
    except (TypeError, ValueError):
        return None


def verdict(e, r):
    if r is None:
        return "FAIL", "missing"
    if r["status"] == "skip":
        return "SKIP", ""
    kind = e["check"].split()
    if kind[0] == "info":
        return "INFO", ""
    if r["status"] != "ok":
        return "FAIL", r["status"]
    v = r["value"]
    if kind[0] == "exact":
        ok = v == e["expected"]
    elif kind[0] == "int":
        try:
            ok = int(v.replace(",", "")) == int(e["expected"].replace(",", ""))
        except ValueError:
            ok = False
    elif kind[0] == "range":
        x = num(v)
        ok = x is not None and float(kind[1]) <= x <= float(kind[2])
    else:
        return "FAIL", f"unknown check {e['check']}"
    return ("PASS", "") if ok else ("FAIL", "value")


def short(s, n):
    s = s or ""
    return s if len(s) <= n else s[: n - 3] + "..."


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--results", default=ART / "out" / "results.tsv")
    ap.add_argument("--expected", default=ART / "expected.tsv")
    ap.add_argument("--stage", nargs="+", action="extend", default=[])
    ap.add_argument("--item", nargs="+", action="extend", default=[], metavar="KEY",
                    help="the items selected in reproduce.sh --item: missing rows of the other "
                    "items of an itemized stage are NOTRUN, not FAIL")
    ap.add_argument("--all-rows", action="store_true", help="also print the PASS rows of the tests stage")
    a = ap.parse_args()
    if not Path(a.results).exists():
        sys.exit(f"check: no results file {a.results}; run artifact/reproduce.sh first")
    res = read_tsv(a.results)
    exp = read_tsv(a.expected)
    stages_run = list(dict.fromkeys(r["stage"] for r in res))
    stages = a.stage or stages_run
    byk = {(r["stage"], r["item"]): r for r in res}
    order = list(dict.fromkeys(e["stage"] for e in exp))
    counts = {}
    fails = notrun = 0
    w = (11, 30, 5, 26, 26, 7, 7)
    print(f"{'stage':<{w[0]}} {'item':<{w[1]}} {'':<{w[2]}} {'value':<{w[3]}} {'expected':<{w[4]}} "
          f"{'wall s':>{w[5]}} {'MiB':>{w[6]}}  reference")
    for st in order:
        if st not in stages:
            continue
        ran = st in stages_run
        c = counts.setdefault(st, {"PASS": 0, "FAIL": 0, "SKIP": 0, "INFO": 0, "wall": 0.0, "peak": 0})
        hidden = 0
        for e in (x for x in exp if x["stage"] == st):
            r = byk.get((st, e["item"]))
            if not ran:
                v, why = "FAIL", "stage not run"
            else:
                v, why = verdict(e, r)
            if (v, why) == ("FAIL", "missing") and a.item and st in ITEMIZED \
                    and e["item"].split(" ")[0] not in a.item:
                v, why = "NOTRUN", "not selected with --item"
            if v == "NOTRUN":
                notrun += 1
            else:
                c[v] += 1
            fails += v == "FAIL"
            if r:
                c["wall"] += num(r["wall_s"]) or 0
                c["peak"] = max(c["peak"], num(r["peak_MiB"]) or 0)
            if st == "tests" and v == "PASS" and not a.all_rows:
                hidden += 1
                continue
            val = r["value"] if r else ""
            print(f"{st:<{w[0]}} {short(e['item'], w[1]):<{w[1]}} {v:<{w[2]}} "
                  f"{short(val, w[3]):<{w[3]}} {short(e['expected'], w[4]):<{w[4]}} "
                  f"{(r or {}).get('wall_s', ''):>{w[5]}} {(r or {}).get('peak_MiB', ''):>{w[6]}}  "
                  f"{e['ref']}" + (f"  [{why}]" if why else ""))
        if hidden:
            print(f"{st:<{w[0]}} ({hidden} more PASS rows; --all-rows prints them)")
        extra = [r for r in res if r["stage"] == st and not any(e["item"] == r["item"] for e in exp if e["stage"] == st)]
        for r in extra:
            print(f"{st:<{w[0]}} {short(r['item'], w[1]):<{w[1]}} {'-':<{w[2]}} {short(r['value'], w[3]):<{w[3]}} "
                  f"{'(no expected value)':<{w[4]}} {r['wall_s']:>{w[5]}} {r['peak_MiB']:>{w[6]}}")
    print()
    print(f"{'stage':<12} {'PASS':>5} {'FAIL':>5} {'SKIP':>5} {'INFO':>5} {'wall s':>8} {'peak GiB':>9}")
    tot = {"PASS": 0, "FAIL": 0, "SKIP": 0, "INFO": 0, "wall": 0.0, "peak": 0}
    for st, c in counts.items():
        print(f"{st:<12} {c['PASS']:>5} {c['FAIL']:>5} {c['SKIP']:>5} {c['INFO']:>5} "
              f"{c['wall']:>8.0f} {c['peak'] / 1024:>9.1f}")
        for k in ("PASS", "FAIL", "SKIP", "INFO", "wall"):
            tot[k] += c[k]
        tot["peak"] = max(tot["peak"], c["peak"])
    print(f"{'total':<12} {tot['PASS']:>5} {tot['FAIL']:>5} {tot['SKIP']:>5} {tot['INFO']:>5} "
          f"{tot['wall']:>8.0f} {tot['peak'] / 1024:>9.1f}")
    if notrun:
        print(f"{notrun} row(s) NOTRUN: items not selected with --item, not counted")
        print("\ncheck: " + ("all rows of the items run pass" if fails == 0 else f"{fails} row(s) FAIL"))
    else:
        print("\ncheck: " + ("all rows pass" if fails == 0 else f"{fails} row(s) FAIL"))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())

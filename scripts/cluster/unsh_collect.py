# /// script
# requires-python = ">=3.11"
# ///
"""Collector of the like-for-like comparison (scripts/cluster/unshortened.sbatch).

Usage (from the repo root):
  uv run scripts/cluster/unsh_collect.py RESULTS_DIR [--tsv OUT.tsv] [--r4 PAPER/tables/fig3_data.csv]

RESULTS_DIR holds one key=value file per instance (INST.txt) as unshortened.sbatch writes it.
Writes the per-instance TSV and prints the medians of the within-job ratios, ours over
cpog-lean-check, for variant B (cpog2lrat --delete --binary: no trim, no mask, no inline) and
variant A (the paper's default --delete --binary --trim --keep --inline), the same per band of
the full certificate's size, B against A, and A against the R4 run of the paper (fig3_data.csv).
Ratios as in scripts/paper_numbers.py: per-instance ratios over the jointly completed runs
(ours proved, cpog-lean-check finished with the right count), zero denominators skipped.
"""
from __future__ import annotations

import argparse
import csv
import math
import statistics
from pathlib import Path

BANDS = [("below 10 MB", 0, 10e6), ("10 to 100 MB", 10e6, 100e6),
         ("100 MB to 1 GB", 100e6, 1e9), ("above 1 GB", 1e9, math.inf)]
COLS = ["instance", "family", "full_cert_mb", "fwd_cert_mb", "lrat_mb_A", "lrat_mb_B",
        "c2l_s_A", "c2l_s_B", "check_s_A", "check_s_B", "lean_s_A", "lean_s_B",
        "lean_gb_A", "lean_gb_B", "vc_s", "vc_gb", "vc_count_ok",
        "part_b_s_A", "part_b_s_B", "part_ac_s_A", "part_ac_s_B",
        "lean_rest_s_A", "lean_rest_s_B", "gen_s", "gen_full_s",
        "cc_s", "cc_gb", "cc_count_ok", "status_A", "status_B", "host"]


def read_kv(p: Path) -> dict[str, str]:
    d: dict[str, str] = {}
    for line in p.read_text(errors="replace").splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            d.setdefault(k, v)
    return d


def fnum(d: dict, k: str) -> float | None:
    try:
        return float(d[k])
    except (KeyError, ValueError):
        return None


def check_s(d: dict, v: str) -> float | None:
    b, ac = fnum(d, f"part_b_ms_{v}"), fnum(d, f"part_ac_ms_{v}")
    if b is not None and ac is not None:
        return (b + ac) / 1e3
    st = d.get(f"stamps_{v}", "").split()
    return (int(st[1]) - int(st[0])) / 1e3 if len(st) == 2 else None


def gib(d: dict, k: str) -> float | None:
    x = fnum(d, k)
    return x / 2**20 if x else None


def row(d: dict) -> dict:
    r = {"instance": d["inst"], "family": int(not d["inst"].startswith("mc2022_")),
         "host": d.get("host", ""), "full_bytes": fnum(d, "full_cpog_bytes"),
         "gen_s": fnum(d, "gen_s"), "gen_full_s": fnum(d, "gen_full_s"),
         "vc_s": fnum(d, "vc_s"), "vc_gb": gib(d, "vc_maxrss_kb"),
         "cc_s": fnum(d, "cc_s"), "cc_gb": gib(d, "cc_maxrss_kb"),
         "vc_ok": d.get("vc_exit") == "0" and d.get("vc_success") == "yes"
         and d.get("vc_count_ok") == "yes",
         "vc_count_ok": d.get("vc_count_ok", ""), "cc_count_ok": d.get("cc_count_ok", ""),
         "full_ok": d.get("gen_full_exit") == "0", "done": d.get("done") == "1"}
    r["full_cert_mb"] = r["full_bytes"] / 1e6 if r["full_bytes"] else None
    r["fwd_cert_mb"] = (fnum(d, "cpog_bytes") or 0) / 1e6 or None
    for v in "AB":
        r[f"status_{v}"] = d.get(f"status_{v}", "missing")
        r[f"ok_{v}"] = r[f"status_{v}"] == "proved"
        r[f"lrat_mb_{v}"] = (fnum(d, f"lrat_bytes_{v}") or 0) / 1e6 or None
        r[f"c2l_s_{v}"] = fnum(d, f"c2l_s_{v}")
        r[f"check_s_{v}"] = check_s(d, v)
        b, ac = fnum(d, f"part_b_ms_{v}"), fnum(d, f"part_ac_ms_{v}")
        r[f"part_b_s_{v}"] = b / 1e3 if b is not None else None
        r[f"part_ac_s_{v}"] = ac / 1e3 if ac is not None else None
        r[f"lean_s_{v}"] = fnum(d, f"lean_s_{v}")
        r[f"lean_gb_{v}"] = gib(d, f"lean_{v}_maxrss_kb")
        # Lean total minus the count_models command (between the two stamps): process start,
        # Mathlib and CountCatcher import (cold or warm page cache), #print axioms
        st = d.get(f"stamps_{v}", "").split()
        r[f"lean_rest_s_{v}"] = (r[f"lean_s_{v}"] - (int(st[1]) - int(st[0])) / 1e3
                                 if len(st) == 2 and r[f"lean_s_{v}"] is not None else None)
    return r


def ratios(rows, num, den):
    out = []
    for r in rows:
        a, b = num(r), den(r)
        if a is None or b is None or b <= 0:
            continue
        out.append(a / b)
    return out


def fmt(x) -> str:
    if x is None:
        return ""
    if isinstance(x, float):
        return f"{x:.3f}" if abs(x) < 1000 else f"{x:.1f}"
    return str(x)


def summary(xs: list[float]) -> str:
    if not xs:
        return "n=0"
    lower = sum(1 for x in xs if x < 1)
    return (f"median {statistics.median(xs):.3g} (min {min(xs):.3g}, max {max(xs):.3g}), "
            f"n={len(xs)}, ours lower on {lower}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("results", type=Path)
    ap.add_argument("--tsv", type=Path)
    ap.add_argument("--r4", type=Path, default=Path("PAPER/tables/fig3_data.csv"))
    a = ap.parse_args()
    rows = sorted((row(read_kv(p)) for p in a.results.glob("*.txt")),
                  key=lambda r: (r["full_bytes"] or 0, r["instance"]))
    if a.tsv:
        a.tsv.parent.mkdir(parents=True, exist_ok=True)
        with a.tsv.open("w", newline="") as f:
            w = csv.writer(f, delimiter="\t", lineterminator="\n")
            w.writerow(COLS)
            for r in rows:
                w.writerow([fmt(r.get(c)) for c in COLS])
        print(f"wrote {a.tsv} ({len(rows)} rows)")
    print(f"instances: {len(rows)}, finished: {sum(r['done'] for r in rows)}, "
          f"proved A: {sum(r['ok_A'] for r in rows)}, proved B: {sum(r['ok_B'] for r in rows)}, "
          f"cpog-lean-check right count: {sum(r['vc_ok'] for r in rows)}, "
          f"full generation ok: {sum(r['full_ok'] for r in rows)}")
    for r in rows:
        if r["done"] and not (r["ok_A"] and r["ok_B"] and r["vc_ok"] and r["full_ok"]):
            print(f"  not complete: {r['instance']} A={r['status_A']} B={r['status_B']} "
                  f"vc_ok={r['vc_ok']} full_ok={r['full_ok']}")
    hosts = sorted({r["host"].split(".")[0] for r in rows})
    print(f"hosts: {' '.join(hosts)}")
    for v in "BA":
        joint = [r for r in rows if r[f"ok_{v}"] and r["vc_ok"]]
        pipe = [r for r in joint if r["full_ok"]]
        print(f"\nvariant {v} (ours over cpog-lean-check, within job), joint n={len(joint)}")
        print("  check alone (part B + parts A, C):",
              summary(ratios(joint, lambda r: r[f"check_s_{v}"], lambda r: r["vc_s"])))
        print("  translation plus Lean total:",
              summary(ratios(joint, lambda r: r[f"c2l_s_{v}"] + r[f"lean_s_{v}"],
                             lambda r: r["vc_s"])))
        print("  pipeline after D4 (gen fwd + translation + Lean vs gen full + checker):",
              summary(ratios(pipe, lambda r: r["gen_s"] + r[f"c2l_s_{v}"] + r[f"lean_s_{v}"],
                             lambda r: r["gen_full_s"] + r["vc_s"])))
        print("  Lean total alone:",
              summary(ratios(joint, lambda r: r[f"lean_s_{v}"], lambda r: r["vc_s"])))
        print("  Lean peak RSS over checker peak RSS:",
              summary(ratios(joint, lambda r: r[f"lean_gb_{v}"], lambda r: r["vc_gb"])))
        print("  medians of absolute values: check "
              f"{statistics.median([r[f'check_s_{v}'] for r in joint]):.2f} s, Lean "
              f"{statistics.median([r[f'lean_s_{v}'] for r in joint]):.1f} s, translator "
              f"{statistics.median([r[f'c2l_s_{v}'] for r in joint]):.2f} s, Lean "
              f"{statistics.median([r[f'lean_gb_{v}'] for r in joint]):.2f} GB, checker "
              f"{statistics.median([r['vc_s'] for r in joint]):.1f} s, Lean outside the command "
              f"{statistics.median([r[f'lean_rest_s_{v}'] for r in joint if r[f'lean_rest_s_{v}'] is not None]):.1f} s")
        for label, lo, hi in BANDS:
            rs = [r for r in joint if lo <= (r["full_bytes"] or 0) < hi]
            if not rs:
                continue
            med = lambda xs: f"{statistics.median(xs):.3g}" if xs else "-"
            print(f"  band {label} (n={len(rs)}): check "
                  f"{med(ratios(rs, lambda r: r[f'check_s_{v}'], lambda r: r['vc_s']))}, "
                  f"translation+Lean "
                  f"{med(ratios(rs, lambda r: r[f'c2l_s_{v}'] + r[f'lean_s_{v}'], lambda r: r['vc_s']))}, "
                  f"Lean total {med(ratios(rs, lambda r: r[f'lean_s_{v}'], lambda r: r['vc_s']))}, "
                  f"Lean RSS {med(ratios(rs, lambda r: r[f'lean_gb_{v}'], lambda r: r['vc_gb']))}, "
                  f"check lower on "
                  f"{sum(1 for x in ratios(rs, lambda r: r[f'check_s_{v}'], lambda r: r['vc_s']) if x < 1)}")
    both = [r for r in rows if r["ok_A"] and r["ok_B"]]
    print(f"\nB over A (n={len(both)}), median (min, max) of per-instance ratios")
    for k in ("lrat_mb", "c2l_s", "check_s", "part_b_s", "lean_s", "lean_gb", "lean_rest_s"):
        xs = ratios(both, lambda r: r[f"{k}_B"], lambda r: r[f"{k}_A"])
        if xs:
            print(f"  {k}: {statistics.median(xs):.3g} ({min(xs):.3g}, {max(xs):.3g}), n={len(xs)}")
    big = [r for r in both if (r["full_bytes"] or 0) >= 100e6]
    xs = ratios(big, lambda r: r["check_s_B"], lambda r: r["check_s_A"])
    if xs:
        print(f"  check_s, full certificate at least 100 MB: {statistics.median(xs):.3g}, n={len(xs)}")
    if a.r4.exists():
        r4 = {x["instance"]: x for x in csv.DictReader(a.r4.open())}
        com = [r for r in rows if r["instance"] in r4 and r["ok_A"] and r["vc_ok"]]
        print(f"\nthis run against R4 (fig3_data.csv), n={len(com)}, median (min, max)")
        for lab, num, den in [
            ("cpog-lean-check time", lambda r: r["vc_s"], lambda r: float(r4[r["instance"]]["vc_s"])),
            ("check A", lambda r: r["check_s_A"], lambda r: float(r4[r["instance"]]["our_check_s"])),
            ("Lean total A", lambda r: r["lean_s_A"], lambda r: float(r4[r["instance"]]["our_lean_total_s"])),
            ("full certificate bytes", lambda r: r["full_bytes"], lambda r: float(r4[r["instance"]]["full_cert_bytes"])),
        ]:
            sel = [r for r in com if float(r4[r["instance"]]["vc_s"]) >= 1.0] if "time" in lab or "A" in lab else com
            xs = ratios(sel, num, den)
            if xs:
                print(f"  {lab}: {statistics.median(xs):.3g} ({min(xs):.3g}, {max(xs):.3g}), "
                      f"n={len(xs)} (time rows: R4 checker at least 1 s)")
        missing = sorted(set(r4) - {r["instance"] for r in rows})
        if missing:
            print(f"  R4 instances without a result here ({len(missing)}): {' '.join(missing)}")


if __name__ == "__main__":
    main()

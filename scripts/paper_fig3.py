# /// script
# requires-python = ">=3.11"
# dependencies = ["matplotlib"]
# ///
"""Figure 3: time ratio count-catcher / cpog-lean-check against certificate size.

Usage (from the repo root): uv run scripts/paper_fig3.py

Reads PAPER/tables/fig3_data.csv (written by scripts/paper_numbers.py) and writes
PAPER/fig/compare.pdf (vector, 12.2 cm x 5.5 cm, LNCS text width) and
PAPER/fig/compare.png (preview). Prints the zero-guard count and the band medians.
"""
from __future__ import annotations

import csv
import statistics
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import LogLocator, NullFormatter

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "PAPER" / "tables" / "fig3_data.csv"
OUT_PDF = ROOT / "PAPER" / "fig" / "compare.pdf"
OUT_PNG = ROOT / "PAPER" / "fig" / "compare.png"

CM = 1 / 2.54
WIDTH, HEIGHT = 12.2 * CM, 4.3 * CM
CHECK_FLOOR = 0.005  # s, substituted for our_check_s == 0
VC_FLOOR = 0.05  # s, substituted for vc_s == 0

# Okabe-Ito, colorblind-safe
C_LEAN = "#0072B2"  # blue
C_CHECK = "#D55E00"  # vermillion

BANDS = [("below 10 MB", 0, 10e6), ("10 to 100 MB", 10e6, 100e6),
         ("100 MB to 1 GB", 100e6, 1e9), ("above 1 GB", 1e9, float("inf"))]


def load():
    rows = list(csv.DictReader(DATA.open()))
    guards = 0
    out = []
    for r in rows:
        chk, vc = float(r["our_check_s"]), float(r["vc_s"])
        guarded = False
        if chk == 0.0:
            chk, guarded = CHECK_FLOOR, True
        if vc == 0.0:
            vc, guarded = VC_FLOOR, True
        guards += guarded
        out.append({
            "instance": r["instance"], "family": r["family"] == "1", "limit": r["limit"],
            "mb": int(r["full_cert_bytes"]) / 1e6,
            "lean_ratio": float(r["our_lean_total_s"]) / vc,
            "check_ratio": chk / vc,
        })
    return out, guards


def report(rows, guards):
    limits = sorted({r["limit"] for r in rows})
    print(f"rows: {len(rows)}, limit values: {limits}, rows with a zero guard: {guards}")
    for label, lo, hi in BANDS:
        sel = [r["lean_ratio"] for r in rows if lo <= r["mb"] * 1e6 < hi]
        print(f"  whole Lean run, {label}: n={len(sel)}, median={statistics.median(sel):.3g}")
    chk = [r["check_ratio"] for r in rows]
    print(f"  check alone: min={min(chk):.3g} median={statistics.median(chk):.3g} "
          f"max={max(chk):.3g}")


def plot(rows):
    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["cmr10"],
        "mathtext.fontset": "cm",
        "axes.formatter.use_mathtext": True,
        "font.size": 8,
        "axes.labelsize": 8,
        "xtick.labelsize": 8,
        "ytick.labelsize": 8,
        "legend.fontsize": 8,
        "axes.linewidth": 0.6,
        "xtick.major.width": 0.6,
        "ytick.major.width": 0.6,
        "xtick.minor.width": 0.4,
        "ytick.minor.width": 0.4,
        "xtick.major.size": 3,
        "ytick.major.size": 3,
        "xtick.minor.size": 1.5,
        "ytick.minor.size": 1.5,
        "pdf.fonttype": 42,
    })
    fig, ax = plt.subplots(figsize=(WIDTH, HEIGHT))
    ax.axhline(1.0, color="0.6", lw=0.6, zorder=0)

    ms = 4  # marker size in points
    for fam, marker in [(False, "o"), (True, "^")]:
        sel = [r for r in rows if r["family"] == fam]
        x = [r["mb"] for r in sel]
        ax.plot(x, [r["lean_ratio"] for r in sel], ls="none", marker=marker, ms=ms,
                mfc=C_LEAN, mec=C_LEAN, mew=0.5, alpha=0.85, zorder=3)
        ax.plot(x, [r["check_ratio"] for r in sel], ls="none", marker=marker, ms=ms,
                mfc="none", mec=C_CHECK, mew=0.7, zorder=2)

    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("certificate size (MB)")
    ax.set_ylabel("time ratio")
    ax.xaxis.set_minor_formatter(NullFormatter())
    ax.yaxis.set_minor_formatter(NullFormatter())
    ax.yaxis.set_major_locator(LogLocator(base=10, numticks=10))
    ax.set_xlim(1e-2, 1e4)
    ax.set_ylim(1e-2, 3e2)

    handles = [
        Line2D([], [], ls="none", marker="o", ms=ms, mfc=C_LEAN, mec=C_LEAN, mew=0.5,
               label="Lean"),
        Line2D([], [], ls="none", marker="o", ms=ms, mfc="none", mec=C_CHECK, mew=0.7,
               label="Check"),
        Line2D([], [], ls="none", marker="o", ms=ms, mfc="0.45", mec="0.45", mew=0.5,
               label="MC2022"),
        Line2D([], [], ls="none", marker="^", ms=ms, mfc="0.45", mec="0.45", mew=0.5,
               label="families"),
    ]
    ax.legend(handles=handles, loc="upper right", ncol=2, frameon=False,
              handletextpad=0.3, columnspacing=1.0, borderaxespad=0.4)
    fig.tight_layout(pad=0.2)
    OUT_PDF.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(OUT_PDF)
    fig.savefig(OUT_PNG, dpi=300)
    plt.close(fig)


def main():
    rows, guards = load()
    report(rows, guards)
    plot(rows)
    print(f"wrote {OUT_PDF.relative_to(ROOT)} and {OUT_PNG.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

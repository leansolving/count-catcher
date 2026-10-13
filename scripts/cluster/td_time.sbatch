#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -J tdtime
#SBATCH -C genoa
#SBATCH -c 2
#SBATCH --mem=16G
#SBATCH -t 06:00:00
#SBATCH -o /home1/szeider/mccert/td/logs/%x.%j.out
# Site defaults of our Slurm cluster; adjust the paths before use elsewhere.
# Phase 2 of the part C comparison (protocol in research/eval-2026-10-01/partc_topdown.md):
# part C by M4, M3, M2, M1 on the POG of phase 1 (td_pog.sbatch), each run in its own process of the native exe
# count-catcher-partc (private copy lean_partc). A check has TO seconds (default 1800); the process
# gets TO + SLACK (default 600) for loading and, for M1, part A, and a result over TO counts as
# a timeout. A run under 60 s is repeated twice more (median of 3 in the report).
# Results: td/results/INST.txt.
# Usage: sbatch --export=ALL,INST=x [--mem=…] [--dependency=afterok:J] td_time.sbatch
set -uo pipefail
TD=/home1/szeider/mccert/td
E=/home1/szeider/mccert/lean_partc/.lake/build/bin/count-catcher-partc
TO=${TO:-1800}; SLACK=${SLACK:-600}
mkdir -p "$TD/results"; OUT=$TD/results/$INST.txt; : > "$OUT"
kv() { echo "$1=$2" >> "$OUT"; }
W=${SLURM_TMPDIR:-/tmp/szeider.$SLURM_JOB_ID}/tdtime_$INST; mkdir -p "$W"; cd "$W" || exit 90
kv host "$(hostname)"; kv cpu "$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs)"
kv affinity "$(taskset -cp $$ | cut -d: -f2 | xargs)"; kv job "$SLURM_JOB_ID"
kv exe_md5 "$(md5sum "$E" | cut -d' ' -f1)"; kv to "$TO"
cp "$TD/pog/$INST.pog" in.pog && cp "$TD/pog/$INST.cnf" in.cnf || { kv status no_input; exit 0; }
for m in m4 m3 m2 m1; do
  for rep in 1 2 3; do
    timeout $((TO + SLACK)) "$E" in.pog in.cnf $m > run.out 2>&1; e=$?
    kv "${m}_r${rep}_exit" $e
    grep -E "^partc-(load|a|m) " run.out | sed "s/^/r$rep /" >> "$OUT"
    ms=$(grep "^partc-m " run.out | head -1 | sed -n 's/.* ms=\([0-9]*\).*/\1/p')
    if [ $e = 124 ] || { [ -n "$ms" ] && [ "$ms" -gt $((TO * 1000)) ]; }; then kv "${m}_status" timeout; break; fi
    [ -n "$ms" ] || { kv "${m}_status" "error:$(tail -c 200 run.out | tr '\n' ' ')"; break; }
    [ "$ms" -ge 60000 ] && break
  done
done
kv status done
cd / && rm -rf "$W"

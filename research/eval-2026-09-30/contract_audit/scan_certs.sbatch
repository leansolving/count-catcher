#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -J scanneg
#SBATCH -c 1
#SBATCH --mem=2G
#SBATCH -t 04:00:00
#SBATCH -C genoa
#SBATCH -o /home1/szeider/mccert/lean_audit/logs/%x.%j.out
# Scan the certificates kept on slurm-cpu01 (/scratch/szeider/mccert_certs, see
# research/eval-2026-09-30/mc2022.md) for negated internal edges, negated roots, constants.
A=/home1/szeider/mccert/lean_audit
OUT=$A/results_scan.txt; : > $OUT
echo "host=$(hostname) start=$(date)" >> $OUT
ls -la /scratch/szeider/mccert_certs >> $OUT 2>&1
find /scratch/szeider/mccert_certs -name '*.cpog' -o -name '*.pog' 2>/dev/null | sort | while read -r f; do
  awk -f $A/audit/scan_negation.awk "$f" >> $OUT 2>&1
done
echo "end=$(date)" >> $OUT

#!/bin/bash
# Run the worklist on gpu01 (no scheduler) with NPAR parallel tasks; scratch on the local disk.
# Usage: run_gpu01.sh WORKLIST NPAR [FIRST LAST [RESULTS]]
set -uo pipefail
A=/home1/szeider/mccert/lean_audit2
WL=$1; NPAR=$2
N=$(wc -l < "$WL"); FIRST=${3:-0}; LAST=${4:-$((N - 1))}; RES=${5:-$A/results}
SCR=/home/scratch/szeider/mccert_audit2; mkdir -p "$SCR"
echo "start $(date) tasks $FIRST..$LAST of $WL, $NPAR parallel, results $RES"
seq "$FIRST" "$LAST" | xargs -P "$NPAR" -I{} bash -c "bash $A/audit/audit_task.sh {} $WL $SCR $RES > $SCR/task_{}.log 2>&1; echo \"task {} exit \$? \$(date +%T)\"; true"
echo "end $(date)"

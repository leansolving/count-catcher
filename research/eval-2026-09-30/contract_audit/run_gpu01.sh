#!/bin/bash
# Run the worklist on gpu01 (no scheduler) with NPAR parallel tasks; scratch on the local disk.
# Usage: run_gpu01.sh WORKLIST NPAR [FIRST LAST]
set -uo pipefail
A=/home1/szeider/mccert/lean_audit
WL=$1; NPAR=$2
N=$(wc -l < "$WL"); FIRST=${3:-0}; LAST=${4:-$((N - 1))}
SCR=/home/scratch/szeider/mccert_audit; mkdir -p "$SCR"
echo "start $(date) tasks $FIRST..$LAST of $WL, $NPAR parallel"
seq "$FIRST" "$LAST" | xargs -P "$NPAR" -I{} bash -c "bash $A/audit/audit_task.sh {} $WL $SCR > $SCR/task_{}.log 2>&1; echo \"task {} exit \$? \$(date +%T)\"; true"
echo "end $(date)"

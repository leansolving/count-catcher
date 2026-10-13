#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -J audit
#SBATCH -c 1
#SBATCH --mem=4G
#SBATCH -t 08:00:00
#SBATCH -o /home1/szeider/mccert/lean_audit/logs/%x.%A_%a.out
# Slurm wrapper for audit_task.sh (one worklist line per array task).
# Usage: sbatch --array=0-47%16 [--export=ALL,WORKLIST=...] audit.sbatch
A=/home1/szeider/mccert/lean_audit
bash "$A/audit/audit_task.sh" "$SLURM_ARRAY_TASK_ID" "${WORKLIST:-$A/audit/worklist.txt}" "${SLURM_TMPDIR:-/tmp/szeider.$SLURM_JOB_ID}"

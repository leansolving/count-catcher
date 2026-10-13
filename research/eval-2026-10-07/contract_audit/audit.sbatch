#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -J audit2
#SBATCH -c 1
#SBATCH --mem=4G
#SBATCH -t 08:00:00
#SBATCH -o /home1/szeider/mccert/lean_audit2/logs/%x.%A_%a.out
# Slurm wrapper for audit_task.sh (one worklist line per array task); alternative to run_gpu01.sh.
# Usage: sbatch --array=0-47%32 [--export=ALL,WORKLIST=...] audit.sbatch
A=/home1/szeider/mccert/lean_audit2
bash "$A/audit/audit_task.sh" "$SLURM_ARRAY_TASK_ID" "${WORKLIST:-$A/audit/worklist.txt}" "${SLURM_TMPDIR:-/tmp/szeider.$SLURM_JOB_ID}"

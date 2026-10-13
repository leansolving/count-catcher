#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -J auditbuild
#SBATCH -c 4
#SBATCH --mem=12G
#SBATCH -t 01:00:00
#SBATCH -o /home1/szeider/mccert/lean_audit/logs/%x.%j.out
# Build the audit driver mccert-audit (AuditMain.lean) and the McCert library in the separate
# copy /home1/szeider/mccert/lean_audit (packages symlinked to the pipeline's, LRATCatcher
# copied). The pipeline's lean/ is never built here.
set -uo pipefail
cd /home1/szeider/mccert/lean_audit || exit 90
export PATH=/home1/szeider/.elan/bin:$PATH
echo "host=$(hostname) start=$(date)"
lake build --no-build LRATCatcher > logs/nobuild_lratcatcher.txt 2>&1; echo "lratcatcher_uptodate_exit=$?"
lake build mccert-audit McCert 2>&1 | tail -15
echo "build_exit=${PIPESTATUS[0]} end=$(date)"

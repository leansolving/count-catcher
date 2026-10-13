#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -J audit2build
#SBATCH -c 4
#SBATCH --mem=12G
#SBATCH -t 01:00:00
#SBATCH -o /home1/szeider/mccert/lean_audit2/logs/%x.%j.out
# Build the driver count-catcher-audit (AuditMain.lean) in the copy /home1/szeider/mccert/lean_audit2
# (cp -a of lean_cc; .lake/packages stays the symlink to lean_final's packages, which are up to
# date, so only AuditMain is compiled). On 2026-10-07 the build ran on slurm-login01 directly
# (two jobs, 15 s): `lake build count-catcher-audit`.
set -uo pipefail
cd /home1/szeider/mccert/lean_audit2 || exit 90
export PATH=/home1/szeider/.elan/bin:$PATH
echo "host=$(hostname) start=$(date)"
lake build --no-build LRATCatcher CountCatcherChecker > logs/nobuild_libs.txt 2>&1; echo "libs_uptodate_exit=$?"
lake build count-catcher-audit 2>&1 | tail -15
echo "build_exit=${PIPESTATUS[0]} end=$(date)"

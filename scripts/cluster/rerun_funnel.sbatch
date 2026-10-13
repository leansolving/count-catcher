#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -J ffunnel
#SBATCH -c 2
#SBATCH --mem=64G
#SBATCH -t 06:00:00
#SBATCH -o /home1/szeider/mccert/final/logs/%x.%A_%a.out
# Site defaults of our Slurm cluster; adjust the paths before use elsewhere.
# MC2022 funnel of the paper rerun (2026-10-02, research/eval-2026-10-02/rerun.md): array task i
# runs e2e.sbatch in DIMACS mode, streamed, on the i-th name of LIST (the 180 unique instances of
# research/eval-2026-09-30/mc2022_list.txt, longest expected first), CNF scope/cnf/mc2022/INST.cnf,
# with the private copies lean_final, tools_final and final/src/<commit>/scripts. Limits: D4
# 4000 s, generator 4000 s (also pog_count.py and the translator), Lean 3600 s. INLINE, CPOG_CHECK
# and the other e2e options pass through the environment; RUN names the result directory.
# Usage: sbatch -C bc5 --array=1-180%24 --export=ALL,INLINE=1 rerun_funnel.sbatch
M=/home1/szeider/mccert
F=$M/final
LIST=${LIST:-$F/funnel_list.txt}
INST=$(sed -n "${SLURM_ARRAY_TASK_ID}p" "$LIST")
[ -n "$INST" ] || { echo "no instance for task $SLURM_ARRAY_TASK_ID"; exit 91; }
export INST FAMILY=dimacs MODE=${MODE:-stream} CNF=$M/scope/cnf/mc2022/$INST.cnf
export LEANDIR=${LEANDIR:-$M/lean_final} TOOLS=${TOOLS:-$M/tools_final/bin}
export SCRIPTS=${SCRIPTS:-$F/src/68fc568/scripts}
export RES=$F/results/${RUN:-funnel}/$INST TO_D4=${TO_D4:-4000} TO_GEN=${TO_GEN:-4000} TO_LEAN=${TO_LEAN:-3600}
exec bash "$F/scripts/e2e.sbatch"

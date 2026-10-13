#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -J latcyc
#SBATCH -c 2
#SBATCH --mem=32G
#SBATCH -t 12:00:00
#SBATCH --exclude=slurm-cpu01
#SBATCH -o /home1/szeider/mccert/latin8/logs/%x.%A_%a.out
# Site defaults of our Slurm cluster; adjust the paths before use elsewhere.
# Reduced Latin squares by the cycle type of the second row (scripts/showcase/latin_cycles.py,
# CountCatcherMath/Families/LatinCycle.lean): one leaf per array task (the task index is the leaf's
# index in OUT/plan.json), or the assembly with ASSEMBLE=1 (one task, after every leaf).
#
# Must be set (or checked) before submitting:
#   OUT      the plan directory on /home1 (default /home1/szeider/mccert/latin8): plan.json from
#            `latin_cycles.py --n 8 --k 3 --plan-only --pilot-d4 d4_all.tsv --out OUT`; results go
#            to OUT/res/LEAF.txt (key=value, small).
#   MOD      the directory of the leaf modules (MOD/Latin8Cyc/LEAF.olean), shared by every task
#            and the assembly, NOT on /home1: a leaf's .olean holds its POG text and keep mask,
#            about the size of its .nnf (measured 9.5 MB for the smallest leaf, 7.5 MB .nnf), so
#            about 145 GB for all 737 leaves (estimate from the pilot's 114 GB of .nnf). No
#            default, must be set. /home1archive is NOT mounted on the Slurm compute nodes and
#            the /home1 quota has no room for it, so use node-local persistent scratch on ONE
#            node and pin every leaf task and the assembly to that node (for example
#            MOD=/scratch/szeider/latin8/mod with `-C genoa`, slurm-cpu01); the modules are
#            only needed until the assembly has been checked.
#   LEANDIR  the Lean package, built (lake build CountCatcher) with the plugins
#            .lake/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.so and
#            .lake/build/lib/libCountCatcher_CountCatcherChecker.so (default /home1/szeider/mccert/lean)
#   TOOLS    d4, cpog-gen-fwd, cpog2lrat (with --keep), cadical, drat-trim
#            (default /home1/szeider/mccert/tools/bin; cpog-gen calls cadical and drat-trim)
#   SCRIPTS  the directory of latin_cycles.py (default /home1/szeider/mccert/scripts/showcase)
#   memory   by tier, with `sbatch --mem=...` (overrides the header). From the D4 pilot
#            (D4 on every leaf, d4_all.tsv; its counts are in plan.json): certificate about 72x the .nnf
#            (62-90), cpog-gen RSS 1.4-1.6x the certificate, Lean peak up to 40-50 GB for the
#            largest leaf (460 MB .nnf, about 52 GB in generation). Tiers by .nnf (plan-only
#            writes the index lists OUT/tier_small.txt and OUT/tier_large.txt):
#              .nnf <= 150 MB (368 leaves): --mem=32G
#              .nnf >  150 MB (369 leaves): --mem=80G
#   scratch  $SLURM_TMPDIR, at least SCRATCH_MIN GB free (default 60; the largest certificate
#            is about 33 GB, plus the LRAT file); the leaf's certificates are deleted after its
#            Lean check.
# Optional: INLINE=0 passes --no-inline (cpog2lrat --inline is the default);
#   TO_D4, TO_GEN, TO_LEAN (seconds per stage, default 0 = none).
# A leaf with a result file that says status=proved is skipped, so the array can be resubmitted
# as a whole after failures. Peak RSS per stage is the child's ru_maxrss (os.wait4 in the
# driver; no /usr/bin/time on the compute nodes); the job's cgroup peak goes to the log.
#
# The log directory of the -o line above must exist (mkdir -p /home1/szeider/mccert/latin8/logs).
# Usage (from the login node, nothing else to run there):
#   python3 $SCRIPTS/latin_cycles.py --n 8 --k 3 --plan-only \
#       --pilot-d4 /home1/szeider/mccert/latin8pilot/d4_all.tsv --out $OUT
#   sbatch --array=$(cat $OUT/tier_small.txt)%40 --mem=32G latin_cycles.sbatch
#   sbatch --array=$(cat $OUT/tier_large.txt)%20 --mem=80G latin_cycles.sbatch
#   (after every leaf:)  sbatch --mem=16G -t 04:00:00 --export=ALL,ASSEMBLE=1 latin_cycles.sbatch
set -uo pipefail
OUT=${OUT:-/home1/szeider/mccert/latin8}
LEANDIR=${LEANDIR:-/home1/szeider/mccert/lean}
TOOLS=${TOOLS:-/home1/szeider/mccert/tools/bin}
MOD=${MOD:?set MOD to a node-local directory visible to every task (see the header)}
SCRIPTS=${SCRIPTS:-/home1/szeider/mccert/scripts/showcase}
export PATH=$TOOLS:/home1/szeider/.elan/bin:$PATH
mkdir -p "$OUT/res" "$OUT/logs"
echo "host=$(hostname) cpu=$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs) start=$(date -Is)"
cg=$(cut -d: -f3 /proc/self/cgroup | head -1)
if [ "${ASSEMBLE:-0}" = 1 ]; then
  python3 "$SCRIPTS/latin_cycles.py" --plan "$OUT/plan.json" --assemble --mod "$MOD" --lean "$LEANDIR" \
    --tools "$TOOLS" --to-lean "${TO_LEAN:-0}"
  rc=$?
else
  I=${SLURM_ARRAY_TASK_ID:?array index = leaf index}
  # WORKBASE: a fixed per-leaf scratch base on the node (the driver works in WORKBASE/LEAF), so
  # that a rerun of a leaf killed by a time limit first deletes its leftover certificates.
  S=${WORKBASE:-${SLURM_TMPDIR:-/tmp/szeider.latcyc.$$}}; mkdir -p "$S"
  free=$(df -BG -P "$S" | tail -1 | awk '{print $4+0}')
  if [ "$free" -lt "${SCRATCH_MIN:-60}" ]; then
    echo "INFRA scratch_free=${free}G host=$(hostname) leaf=$I" >> "$OUT/INFRA.txt"; exit 3
  fi
  FL=(); [ "${INLINE:-1}" = 0 ] && FL=(--no-inline)
  python3 "$SCRIPTS/latin_cycles.py" --plan "$OUT/plan.json" --leaf "$I" --scratch "$S" --mod "$MOD" \
    --lean "$LEANDIR" --tools "$TOOLS" --to-d4 "${TO_D4:-0}" --to-gen "${TO_GEN:-0}" \
    --to-lean "${TO_LEAN:-0}" ${FL[@]+"${FL[@]}"}
  rc=$?
  # with a shared WORKBASE this would delete the certificates of leaves still running
  # (latin8c_*: the leaf prefix of plans written before 2026-10-05)
  [ -n "${WORKBASE:-}" ] || rm -rf "$S"/latin8_* "$S"/latin8c_* 2>/dev/null
fi
echo "rc=$rc cgroup_peak=$(cat /sys/fs/cgroup${cg}/memory.peak 2>/dev/null || echo unknown) end=$(date -Is)"
exit $rc

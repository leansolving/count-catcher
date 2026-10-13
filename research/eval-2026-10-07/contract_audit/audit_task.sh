#!/bin/bash
# One differential-test task (difftest_rerun.md). Usage: audit_task.sh INDEX WORKLIST SCRATCH [RESULTS]
# Line INDEX+1 of WORKLIST is "SET SHARD NSHARDS COUNT MUT [SAMPLE]". difftest.py runs D4, cpog-gen-fwd
# and the native translator (text and default flags) on every formula of the shard (or of the
# sample, SAMPLE > 0) and writes the bundle (with mutants) to SCRATCH; count-catcher-audit checks
# the bundle in one process. The stream reader's block size cycles through 1, 2, 3 and 4096 lines
# (text) or actions (binary) with INDEX. Results (gzipped) in RESULTS/SET_SHARD/ (default
# lean_audit2/results). Called by audit.sbatch (Slurm, SCRATCH = $SLURM_TMPDIR) and run_gpu01.sh.
set -uo pipefail
I=$1; WL=$2; SCR=$3
A=/home1/szeider/mccert/lean_audit2
RES=${4:-$A/results}
read -r SET SHARD NSH COUNT MUT SAMPLE <<< "$(sed -n "$((I + 1))p" "$WL")"
[ -n "${SET:-}" ] || { echo "no work line $I"; exit 0; }
SAMPLE=${SAMPLE:-0}
BLOCKS=(1 2 3 4096); BLOCK=${BLOCKS[$((I % 4))]}
W=$SCR/audit_${SET}_${SHARD}
R=$RES/${SET}_${SHARD}
rm -rf "$W"; mkdir -p "$W" "$R"
echo "host=$(hostname) set=$SET shard=$SHARD/$NSH count=$COUNT mut=$MUT sample=$SAMPLE block=$BLOCK start=$(date +%s)" > "$R/info.txt"
# peak memory per step when GNU time is there (gpu01; not on the Slurm compute nodes)
TM=(); [ -x /usr/bin/time ] && TM=(/usr/bin/time -f %M -o "$W/maxrss_difftest")
t0=$(date +%s)
"${TM[@]}" /home1/szeider/.local/bin/uv run -q --no-project "$A/audit/difftest.py" "$SET" "$SHARD" "$NSH" "$W" \
  --tools /home1/szeider/mccert/tools_final/bin --count "$COUNT" --mut "$MUT" --seed 1 \
  --plainsample 0.05 --sample "$SAMPLE" > "$W/difftest.log" 2>&1
echo "difftest_exit=$? difftest_s=$(( $(date +%s) - t0 )) bundle_bytes=$(stat -c %s "$W/bundle") difftest_maxrss_kb=$(tail -1 "$W/maxrss_difftest" 2>/dev/null)" >> "$R/info.txt"
[ -x /usr/bin/time ] && TM=(/usr/bin/time -f %M -o "$W/maxrss_lean")
t1=$(date +%s)
LRATCATCHER_STREAM_BLOCK=$BLOCK "${TM[@]}" "$A/.lake/build/bin/count-catcher-audit" "$W/bundle" "$W" > "$W/lean.out" 2> "$W/lean.err"
echo "lean_exit=$? lean_s=$(( $(date +%s) - t1 )) lean_maxrss_kb=$(tail -1 "$W/maxrss_lean" 2>/dev/null) lean_err_panics=$(grep -c 'index out of bounds' "$W/lean.err")" >> "$R/info.txt"
tail -1 "$W/lean.out" >> "$R/info.txt"
cat "$W/difftest.log" >> "$R/info.txt"
head -c 2000 "$W/lean.err" > "$R/lean.err"
gzip -c "$W/lean.out" > "$R/lean.out.gz"
gzip -c "$W/tools.tsv" > "$R/tools.tsv.gz"
echo "end=$(date +%s)" >> "$R/info.txt"
rm -rf "$W"

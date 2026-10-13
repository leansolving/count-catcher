#!/bin/bash
# One differential-test task (contract_audit.md, part 3). Usage: audit_task.sh INDEX WORKLIST SCRATCH
# Line INDEX+1 of WORKLIST is "SET SHARD NSHARDS COUNT MUT". difftest.py runs D4, cpog-gen and the
# native translator on every formula of the shard and writes the bundle (with mutants) to
# SCRATCH; mccert-audit checks the bundle in one process. The stream reader's block size cycles
# through 1, 2, 3 and 4096 lines with INDEX. Results (gzipped) in lean_audit/results/SET_SHARD/.
# Called by audit.sbatch (Slurm, SCRATCH = $SLURM_TMPDIR) and run_gpu01.sh.
set -uo pipefail
I=$1; WL=$2; SCR=$3
A=/home1/szeider/mccert/lean_audit
read -r SET SHARD NSH COUNT MUT <<< "$(sed -n "$((I + 1))p" "$WL")"
[ -n "${SET:-}" ] || { echo "no work line $I"; exit 0; }
BLOCKS=(1 2 3 4096); BLOCK=${BLOCKS[$((I % 4))]}
W=$SCR/audit_${SET}_${SHARD}
R=$A/results/${SET}_${SHARD}
rm -rf "$W"; mkdir -p "$W" "$R"
echo "host=$(hostname) set=$SET shard=$SHARD/$NSH count=$COUNT mut=$MUT block=$BLOCK start=$(date +%s)" > "$R/info.txt"
t0=$(date +%s)
/home1/szeider/.local/bin/uv run -q --no-project "$A/audit/difftest.py" "$SET" "$SHARD" "$NSH" "$W" \
  --tools /home1/szeider/mccert/tools/bin --count "$COUNT" --mut "$MUT" --seed 1 \
  --py "$A/audit/cpog2lrat.py" --pysample 0.02 --delsample 0.05 > "$W/difftest.log" 2>&1
echo "difftest_exit=$? difftest_s=$(( $(date +%s) - t0 )) bundle_bytes=$(stat -c %s "$W/bundle")" >> "$R/info.txt"
t1=$(date +%s)
LRATCATCHER_STREAM_BLOCK=$BLOCK "$A/.lake/build/bin/mccert-audit" "$W/bundle" "$W" > "$W/lean.out" 2> "$W/lean.err"
echo "lean_exit=$? lean_s=$(( $(date +%s) - t1 ))" >> "$R/info.txt"
tail -1 "$W/lean.out" >> "$R/info.txt"
cat "$W/difftest.log" >> "$R/info.txt"
head -c 2000 "$W/lean.err" > "$R/lean.err"
gzip -c "$W/lean.out" > "$R/lean.out.gz"
gzip -c "$W/tools.tsv" > "$R/tools.tsv.gz"
cp "$W/pydiff.tsv" "$R/pydiff.tsv"
echo "end=$(date +%s)" >> "$R/info.txt"
rm -rf "$W"

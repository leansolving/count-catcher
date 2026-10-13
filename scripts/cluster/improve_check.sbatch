#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -C genoa
#SBATCH -J ovnchk
#SBATCH -c 2
#SBATCH --mem=32G
#SBATCH -t 02:00:00
#SBATCH -o /home1/szeider/mccert/ovn/logs/%x.%j.out
# Site defaults of our Slurm cluster; adjust the paths before use elsewhere.
# Before/after measurements, job type C: one translator variant and one Lean checker on the
# certificate that improve_gen.sbatch stored for INSTANCE on slurm-cpu01 (hence -C genoa).
#   improve_check.sbatch INSTANCE VARIANT LEANDIR TRANSLATOR [FLAGS...]
# 1. TRANSLATOR ../in.cnf ../cert.cpog fwd FLAGS in /scratch/szeider/mccert_ovn/INSTANCE/VARIANT/
#    (timeout TO_C2L, default 3000 s): wall s, CPU s, peak RSS, bytes of every fwd.* file, its
#    stdout and stderr (statistics). fwd.cnf is deleted (the theorem reads in.cnf).
# 2. Theorem file, streamed DIMACS form: `TLPY dimacs in.cnf stream COUNT fwd.pog fwd.lrat
#    ovn_INSTANCE > T.lean`; TLPY defaults to theorem_lean.py of a4345a1 (ovn/src_base/scripts).
#    COUNT from gen.done; WRONG=1 states COUNT+1, and the run must then be rejected.
# 3. `lake env lean` in LEANDIR with LEANDIR's plugins (LRATCatcher, CountCatcherChecker), timeout TO_LEAN
#    (default: the job's remaining time minus 5 minutes).
# Records part B and parts A+C from the three stamps of the theorem file, pre_s (Lean start to
# the first stamp: imports and the POG include_str), post_s (last stamp to exit), Lean wall, CPU,
# peak RSS of lake+lean, exit, count, #print axioms, and the provenance: host, uptime at start
# and end, LEANDIR/OVN_SOURCE (source commit), LRATCatcher rev, sha256 of both plugins, of the
# translator and of TLPY. Result: ovn/results/INSTANCE.VARIANT.REP.txt (REP env, default 1;
# WRONG=1: INSTANCE.VARIANT.wrong.REP.txt), ending with status=proved | wrong_rejected |
# WRONG_ACCEPTED | c2l_fail:E | lean_fail:E | ...; T.lean and lean.out go to ovn/results/aux/.
# Translator statistics: every key=N token of its output as c2l_KEY (cpog2lrat --trim/--keep
# print additions_kept, additions_total, cited_input, input_clauses, cited_defs, def_clauses,
# keep_ones, keep_len). If the translator wrote fwd.keep (cpog2lrat --keep), TLPY gets
# `--keep fwd.keep` (theorem_lean.py of f27bb46 or later: part B on the masked clauses).
# GENTAG (default empty): use cert$GENTAG.cpog and gen$GENTAG.done, e.g. GENTAG=_m for the
# monolithic certificate of improve_gen.sbatch with GENTAG=_m.
# Jobs on one INSTANCE/VARIANT serialize on a lock; chain repetitions with --dependency.
# KEEP_OUT=0 deletes fwd.lrat at the end (default: kept until the next run of the variant).
# Usage: sbatch [--mem=64G] [-J ovnL3 --dependency=afterok:GENJOB,singleton] \
#          --export=ALL,REP=1 /home1/szeider/mccert/ovn/scripts/improve_check.sbatch q13 base \
#          /home1/szeider/mccert/lean_ovn_base /home1/szeider/mccert/tools_ovn/base/cpog2lrat --delete
set -uo pipefail
INST=${1:?usage: improve_check.sbatch INSTANCE VARIANT LEANDIR TRANSLATOR [FLAGS...]}
VAR=${2:?variant}; LEANDIR=${3:?leandir}; TR=${4:?translator}; shift 4; FLAGS=("$@")
O=/home1/szeider/mccert/ovn
D=/scratch/szeider/mccert_ovn/$INST; W=$D/$VAR
REP=${REP:-1}; WRONG=${WRONG:-0}; GT=${GENTAG:-}
CERT=cert$GT.cpog; DONE=gen$GT.done
TLPY=${TLPY:-$O/src_base/scripts/theorem_lean.py}
PY=$(command -v python3 || echo "/home1/szeider/.local/bin/uv run -q --no-project python")
STAGE="$PY $O/scripts/improve_stage.py"
export PATH=/home1/szeider/.elan/bin:$PATH
TAG=$INST.$VAR.$REP; [ "$WRONG" = 1 ] && TAG=$INST.$VAR.wrong.$REP
R=$O/results/$TAG.txt; A=$O/results/aux
mkdir -p "$O/results" "$A" || exit 2
: > "$R"
kv() { echo "$1=$2" >> "$R"; }
get() { grep "^$1=" "$R" | tail -1 | cut -d= -f2-; }
fin() {
  kv status "$1"; kv uptime_end "$(uptime)"
  local cg; cg=$(cut -d: -f3 /proc/self/cgroup | head -1)
  kv mem_peak_job "$(cat /sys/fs/cgroup${cg}/memory.peak 2>/dev/null || echo unknown)"
  [ "${KEEP_OUT:-1}" = 0 ] && rm -f "$W/fwd.lrat"
  [ -n "${SLURM_TMPDIR:-}" ] && rmdir "$SLURM_TMPDIR" 2>/dev/null
  exit 0
}
sha() { sha256sum "$1" 2>/dev/null | cut -d' ' -f1; }
T0=$(date +%s)
kv inst "$INST"; kv variant "$VAR"; kv rep "$REP"; kv wrong "$WRONG"; kv job "${SLURM_JOB_ID:-none}"
kv host "$(hostname)"; kv uptime_start "$(uptime)"; kv date "$(date -Is)"
kv cpu "$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs)"
kv affinity "$(taskset -cp $$ | cut -d: -f2 | xargs)"; kv mem_limit_mb "${SLURM_MEM_PER_NODE:-unknown}"
kv leandir "$LEANDIR"; kv lean_source "$(head -c 200 "$LEANDIR/OVN_SOURCE" 2>/dev/null | tr '\n' ' ')"
kv lratcatcher_rev "$(git -C "$LEANDIR/.lake/packages/LRATCatcher" rev-parse HEAD 2>/dev/null)"
L=$LEANDIR/.lake
PL1=$L/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.so
PL2=$L/build/lib/libCountCatcher_CountCatcherChecker.so
kv sha256_plugin_lratcatcher "$(sha "$PL1")"; kv sha256_plugin_countcatcher "$(sha "$PL2")"
kv translator "$TR"; kv sha256_translator "$(sha "$TR")"; kv flags "${FLAGS[*]}"
kv tlpy "$TLPY"; kv sha256_tlpy "$(sha "$TLPY")"; kv python "$PY"
kv cert "$CERT"
[ -s "$D/$DONE" ] && [ -s "$D/$CERT" ] || fin no_cert
kv cnf_sha256 "$(sha "$D/in.cnf")"; kv cpog_bytes "$(stat -c %s "$D/$CERT")"
kv scratch_free_gb "$(df -BG -P "$D" | tail -1 | awk '{print $4+0}')"
N=$(cat "$D/$DONE"); NN=$N
[ "$WRONG" = 1 ] && NN=$($PY -c "print($N + 1)")
kv count "$NN"
exec 9> "$D/.$VAR.lock"
flock -w 3600 9 || fin lock_timeout
mkdir -p "$W" && cd "$W" || fin no_workdir
rm -f fwd.* c2l.log T.lean lean.out
# 1. translator
$STAGE "$R" c2l "${TO_C2L:-3000}" c2l.log "$TR" ../in.cnf "../$CERT" fwd "${FLAGS[@]}"; e=$?
kv c2l_log "$(head -c 1500 c2l.log | tr '\n' ' ')"
head -c 20000 c2l.log | grep -o '[a-z_]*=[0-9][0-9]*' | sed 's/^/c2l_/' >> "$R"
kv out_bytes "$(for f in fwd.*; do [ -e "$f" ] && printf '%s:%s ' "$f" "$(stat -c %s "$f")"; done)"
[ "$e" = 0 ] || fin "c2l_fail:$e"
kv lrat_bytes "$(stat -c %s fwd.lrat 2>/dev/null)"; kv pog_bytes "$(stat -c %s fwd.pog 2>/dev/null)"
rm -f fwd.cnf
# 2. theorem file
KF=(); [ -e fwd.keep ] && KF=(--keep "$W/fwd.keep")
kv keep_file "${KF[*]}"
$PY "$TLPY" "${KF[@]}" dimacs "$D/in.cnf" stream "$NN" fwd.pog fwd.lrat "ovn_$INST" > T.lean || fin theorem_file
cp T.lean "$A/$TAG.T.lean"
# 3. Lean
TO=${TO_LEAN:-}
if [ -z "$TO" ]; then
  if [ -n "${SLURM_JOB_END_TIME:-}" ]; then TO=$(( SLURM_JOB_END_TIME - $(date +%s) - 300 ))
  else TO=$(( 7200 - ($(date +%s) - T0) - 300 )); fi
fi
kv lean_timeout "$TO"
cd "$LEANDIR" || fin no_leandir
$STAGE "$R" lean "$TO" "$W/lean.out" lake env lean "--plugin=$PL1" "--plugin=$PL2" "$W/T.lean"; e=$?
head -c 200000 "$W/lean.out" > "$A/$TAG.lean.out"
mapfile -t ST < <(grep '^stamp ' "$W/lean.out" | awk '{print $2}')
kv stamps "${ST[*]}"
if [ "${#ST[@]}" -ge 3 ]; then
  m0=$(get lean_mono0_ms); m1=$(get lean_mono1_ms)
  kv pre_s "$(awk -v a="$m0" -v b="${ST[0]}" 'BEGIN{printf "%.1f", (b-a)/1000}')"
  kv partB_s "$(awk -v a="${ST[0]}" -v b="${ST[1]}" 'BEGIN{printf "%.1f", (b-a)/1000}')"
  kv partAC_s "$(awk -v a="${ST[1]}" -v b="${ST[2]}" 'BEGIN{printf "%.1f", (b-a)/1000}')"
  kv post_s "$(awk -v a="${ST[2]}" -v b="$m1" 'BEGIN{printf "%.1f", (b-a)/1000}')"
fi
kv axioms "$(awk '/depends on axioms/{f=1} f{printf "%s ", $0} f&&/\]/{exit}' "$W/lean.out" | head -c 1500)"
kv lean_errors "$(grep -c 'error' "$W/lean.out")"
kv lean_out "$(grep -v '^stamp ' "$W/lean.out" | head -c 800 | tr '\n' ' ')"
ok=no
[ "$e" = 0 ] && grep -q "ovn_${INST//[^A-Za-z0-9]/_}_models' depends on axioms" "$W/lean.out" \
  && ! grep -q -e "error" -e "sorryAx" "$W/lean.out" && ok=yes
if [ "$WRONG" = 1 ]; then
  [ "$ok" = yes ] && fin WRONG_ACCEPTED
  fin wrong_rejected
fi
[ "$ok" = yes ] && fin proved
case "$e" in 124) fin lean_timeout ;; 137) fin lean_killed ;; *) fin "lean_fail:$e" ;; esac

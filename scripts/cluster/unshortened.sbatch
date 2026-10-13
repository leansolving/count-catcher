#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -J unsh
#SBATCH -c 2
#SBATCH --mem=32G
#SBATCH -t 06:00:00
#SBATCH -o /home1/szeider/mccert/unsh/logs/%x.%A_%a.out
# Site defaults of our Slurm cluster; adjust the paths before use elsewhere.
# Like-for-like comparison with CPOG's verified checker (2026-10-05): e2e.sbatch's
# pipeline with CPOG_CHECK=1, but the forward certificate is translated twice and checked twice:
#   variant B  cpog2lrat --delete --binary                          (no trim, no mask, no inline)
#   variant A  cpog2lrat --delete --binary --trim --keep --inline   (the paper's default)
# Per instance, in this order: D4; cpog-gen-fwd -F -T 500 -G (forward certificate); pog_count.py;
# translation B, translation A (the forward certificate is then deleted); Lean on B (the first
# Lean run of the job, as the single Lean run of the R4 jobs), Lean on A; full certificate from
# the same D4 output by the unpatched cpog-gen; cpog-check and cpog-lean-check on it (each at
# most TO_BASE seconds). Theorem files by theorem_lean.py --command, identical for A and B apart
# from the LRAT, the POG path and A's keep mask. One key=value file per instance, written as
# the job goes: RESDIR/INST.txt (variant fields end in _A or _B; full-certificate fields as in
# cpog_baseline.txt of e2e.sbatch, full_cpog_bytes for the full certificate's size).
# Environment:
#   LIST    file of lines "INST FAMILY ARG [DESC]" (ARG "-" for none), line SLURM_ARRAY_TASK_ID;
#           or INST, FAMILY, ARG, DESC directly
#   CNF     default scope/cnf/mc2022/INST.cnf for FAMILY=dimacs, else scope/cnf/INST.cnf
#   LEANDIR the Lean package with CountCatcher built (default lean_cc); SCRIPTS the directory of
#           theorem_lean.py and pog_count.py (default cc_repo/scripts); TOOLS directory put first
#           on PATH (default tools_final/bin, the tools of the R4 comparison)
#   TO_D4, TO_GEN (also pog_count.py and the translator), TO_LEAN, TO_BASE  defaults 4000, 4000,
#           3600, 3600 (as in R4); WALL the job's time limit in seconds (default 21000)
#   ORDER   "B A" (default) or "A B": order of the two Lean runs
# Usage: sbatch -C bc4 --array=1-82%16 --export=ALL,LIST=/home1/szeider/mccert/unsh/list_mc.txt unshortened.sbatch
set -uo pipefail
M=/home1/szeider/mccert
S=$M/scope
UV=/home1/szeider/.local/bin/uv
RESDIR=${RESDIR:-$M/unsh/results}
if [ -n "${LIST:-}" ]; then
  read -r INST FAMILY ARG DESC <<< "$(sed -n "${SLURM_ARRAY_TASK_ID}p" "$LIST")"
  [ -n "${INST:-}" ] || { echo "no instance for task $SLURM_ARRAY_TASK_ID"; exit 91; }
fi
[ "${ARG:-}" = - ] && ARG=""; ARG=${ARG:-}; DESC=${DESC:-}
if [ "$FAMILY" = dimacs ]; then CNF=${CNF:-$S/cnf/mc2022/$INST.cnf}; else CNF=${CNF:-$S/cnf/$INST.cnf}; fi
LEANDIR=${LEANDIR:-$M/lean_cc}; SCRIPTS=${SCRIPTS:-$M/cc_repo/scripts}
TOOLS=${TOOLS:-$M/tools_final/bin}
TO_D4=${TO_D4:-4000}; TO_GEN=${TO_GEN:-4000}; TO_LEAN=${TO_LEAN:-3600}; TO_BASE=${TO_BASE:-3600}
WALL=${WALL:-21000}; ORDER=${ORDER:-B A}
GEN_BIN=cpog-gen-fwd; GEN_FL="-F -T 500 -G"; GEN_FULL_BIN=cpog-gen
FL_A="--delete --binary --trim --keep --inline"; FL_B="--delete --binary"
export PATH=$TOOLS:$PATH
mkdir -p "$RESDIR"; R_=$RESDIR/$INST.txt; : > "$R_"
kv() { echo "$1=$2" >> "$R_"; }
now() { date +%s.%N; }
dt() { awk -v a="$1" -v b="$(now)" 'BEGIN{printf "%.1f", b-a}'; }
cg=$(cut -d: -f3 /proc/self/cgroup | head -1)
peak() { kv "mem_peak_$1" "$(cat /sys/fs/cgroup${cg}/memory.peak 2>/dev/null || echo unknown)"; }
W=${SLURM_TMPDIR:-/tmp/szeider.${SLURM_JOB_ID:-$$}}/$INST; mkdir -p "$W"; cd "$W" || exit 90
T0=$(date +%s)
# run OUT TO cmd...: wall, exit, peak RSS in KB of cmd (getrusage of the children; no
# /usr/bin/time on the compute nodes), as in e2e.sbatch
PYRUN='import resource, subprocess, sys, time
cmd = ["timeout", sys.argv[2]] + sys.argv[3:]
t = time.time()
with open(sys.argv[1], "w") as f:
    rc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT).returncode
print("%.1f %d %d" % (time.time() - t, rc, resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss))'
sha() { if [ -f "$1" ]; then sha256sum "$1" | cut -c1-64; else echo missing; fi; }
remaining() { local to=$(( T0 + WALL - 300 - $(date +%s) )); [ "$to" -gt "$TO_BASE" ] && to=$TO_BASE; echo "$to"; }
# The full certificate and CPOG's two checkers (e2e.sbatch's base(), fields in this file).
base() {
  [ -s "$W/in.nnf" ] || return 0
  cd "$W" || return 0
  local s e m to C
  to=$(remaining)
  if [ "$to" -lt 60 ]; then kv gen_full_exit skipped_walltime; rm -f in.nnf; return 0; fi
  mkdir -p full && cd full || return 0
  read -r s e m <<< "$($UV run -q --no-project python -c "$PYRUN" gen_full.log "$to" "$GEN_FULL_BIN" ../in.cnf ../in.nnf ../cert.cpog)"
  cd "$W"; rm -f in.nnf
  kv gen_full_bin "$GEN_FULL_BIN"; kv sha256_gen_full "$(sha "$(command -v "$GEN_FULL_BIN")")"
  kv gen_full_s "$s"; kv gen_full_exit "$e"; kv gen_full_maxrss_kb "$m"; kv gen_full_timeout "$to"
  kv full_cpog_bytes "$(stat -c %s cert.cpog 2>/dev/null)"
  if [ "$e" != 0 ] || [ ! -s cert.cpog ]; then
    kv gen_full_tail "$(tail -c 300 full/gen_full.log | tr '\n' ' ')"; rm -rf full cert.cpog; return 0
  fi
  rm -rf full
  kv sha256_cpog_check "$(sha "$(command -v cpog-check)")"
  kv sha256_cpog_lean_check "$(sha "$(command -v cpog-lean-check)")"
  for c in cc vc; do
    to=$(remaining)
    if [ "$to" -lt 60 ]; then kv "${c}_exit" skipped_walltime; continue; fi
    if [ $c = cc ]; then read -r s e m <<< "$($UV run -q --no-project python -c "$PYRUN" cc.out "$to" cpog-check in.cnf cert.cpog)"
    else read -r s e m <<< "$($UV run -q --no-project python -c "$PYRUN" vc.out "$to" cpog-lean-check -c in.cnf cert.cpog)"; fi
    kv "${c}_s" "$s"; kv "${c}_exit" "$e"; kv "${c}_maxrss_kb" "$m"; kv "${c}_timeout" "$to"
    if [ $c = cc ]; then
      kv cc_success "$(grep -q 'FULL-PROOF SUCCESS' cc.out && echo yes || echo no)"
      C=$(grep -m1 'Regular model count = ' cc.out | sed 's/.*= *//')
    else
      kv vc_success "$(grep -q '^PROOF SUCCESSFUL' vc.out && echo yes || echo no)"
      C=$(grep -m1 '^Model count: ' vc.out | sed 's/^Model count: *//')
    fi
    kv "${c}_count_ok" "$([ -n "${N:-}" ] && [ "$C" = "$N" ] && echo yes || echo no)"
    [ "$C" = "${N:-}" ] || kv "${c}_count" "$(echo "$C" | head -c 2000)"
    kv "${c}_tail" "$(tail -c 300 $c.out | tr '\n' ' ')"
  done
  rm -f cert.cpog
}
fin() { kv status "$1"; peak final; base; kv job_s "$(( $(date +%s) - T0 ))"; kv done 1; cd / && rm -rf "$W"; exit 0; }
why() { case "$1" in 124) echo timeout ;; 137) echo killed ;; *) echo "fail:$1" ;; esac; }
tmo() { if [ "$1" = 0 ]; then shift; "$@"; else timeout "$@"; fi; }
# rss NAME TO cmd...: as in e2e.sbatch, NAME_maxrss_kb is the peak RSS of the largest process
# of the stage (ru_maxrss of the children; lean under lake env included)
RSSPY='import resource, subprocess, sys
rc = subprocess.run(sys.argv[3:]).returncode
with open(sys.argv[1], "a") as f:
    f.write("%s_maxrss_kb=%d\n" % (sys.argv[2], resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss))
sys.exit(rc if rc >= 0 else 128 - rc)'
rss() { local n=$1 t=$2; shift 2; [ "$t" = 0 ] || set -- timeout "$t" "$@"; $UV run -q --no-project python -c "$RSSPY" "$R_" "$n" "$@"; }
kv inst "$INST"; kv host "$(hostname)"; kv cpu "$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs)"
kv affinity "$(taskset -cp $$ | cut -d: -f2 | xargs)"; kv slurm_job "${SLURM_JOB_ID:-}"
kv family "$FAMILY $ARG"; kv order "$ORDER"; kv flags_A "$FL_A"; kv flags_B "$FL_B"
kv leandir "$LEANDIR"
kv lean_commit "$(git -C "$LEANDIR" rev-parse HEAD 2>/dev/null || echo unknown)"
kv lratcatcher_rev "$($UV run -q --no-project python -c 'import json, sys
print(next(p["rev"] for p in json.load(open(sys.argv[1]))["packages"] if p["name"] == "LRATCatcher"))' "$LEANDIR/lake-manifest.json" 2>/dev/null || echo unknown)"
L=$LEANDIR/.lake
PLUG_LC=$L/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.so
PLUG_MC=$L/build/lib/libCountCatcher_CountCatcherChecker.so
kv sha256_plugin_lratcatcher "$(sha "$PLUG_LC")"; kv sha256_plugin_countcatcher "$(sha "$PLUG_MC")"
kv translator "$(command -v cpog2lrat)"; kv sha256_translator "$(sha "$(command -v cpog2lrat)")"
kv tools "$TOOLS"; kv sha256_d4 "$(sha "$(command -v d4)")"
kv gen_bin "$(command -v "$GEN_BIN")"; kv sha256_gen "$(sha "$(command -v "$GEN_BIN")")"
kv scripts "$SCRIPTS"; kv sha256_theorem_lean "$(sha "$SCRIPTS/theorem_lean.py")"
U=$(cpog2lrat 2>&1); [[ $U == *--inline* ]] || fin "c2l_lacks_inline"
kv scratch_free "$(df -hP . | tail -1 | awk '{print $4}')"
[ "$(df -BG -P . | tail -1 | awk '{print $4+0}')" -ge "${SCRATCH_MIN:-40}" ] || fin "infra_scratch"
kv cnf "$CNF"
cp "$CNF" in.cnf || fin "no_cnf"
kv vars "$(awk '/^p cnf/{print $3; exit}' in.cnf)"; kv clauses "$(awk '/^p cnf/{print $4; exit}' in.cnf)"
[ "$FAMILY" = edges ] && cp "$CNF" "$INST.cnf" && cp "${CNF%.cnf}.edges" "$INST.edges"
t=$(now); rss d4 "$TO_D4" d4 in.cnf -dDNNF -out=in.nnf > d4.log 2>&1; e=$?
kv d4_exit "$e"; kv d4_s "$(dt $t)"; peak d4
N=$(grep -m1 '^s ' d4.log | awk '{print $2}'); kv count "$N"
[ "$e" = 0 ] && [ -n "$N" ] && [ -s in.nnf ] || fin "d4_$(why $e)"
t=$(now); rss gen "$TO_GEN" $GEN_BIN $GEN_FL in.cnf in.nnf cert.cpog > gen.log 2>&1; e=$?
kv gen_exit "$e"; kv gen_s "$(dt $t)"; peak gen
kv pog_defs "$(grep -m1 'Compressed POG has' gen.log | sed 's/.* and \([0-9]*\) defining clauses.*/\1/')"
kv cpog_bytes "$(stat -c %s cert.cpog 2>/dev/null)"
if [ "$e" != 0 ]; then kv gen_tail "$(tail -c 300 gen.log | tr '\n' ' ')"; rm -f cert.cpog; fin "gen_$(why $e)"; fi
t=$(now); tmo "$TO_GEN" $UV run -q --no-project "$SCRIPTS/pog_count.py" in.cnf cert.cpog > pc.txt 2>&1; e=$?
PC=$(head -c 100000 pc.txt)
kv pog_count_ok "$([ "$PC" = "$N" ] && echo yes || echo "no:$(why $e):$(head -c 200 pc.txt)")"
kv pog_count_s "$(dt $t)"
[ "$PC" != "$N" ] && [[ "$PC" =~ ^[0-9]+$ ]] && N=$PC && kv count_used "$N"
# The two translations of the same forward certificate
for V in B A; do
  if [ $V = A ]; then FL=$FL_A; else FL=$FL_B; fi
  t=$(now); rss "c2l_$V" "$TO_GEN" cpog2lrat in.cnf cert.cpog "fwd$V" $FL > "c2l_$V.log" 2>&1; e=$?
  kv "c2l_exit_$V" "$e"; kv "c2l_s_$V" "$(dt $t)"
  kv "c2l_out_$V" "$(tr '\n' ' ' < "c2l_$V.log" | head -c 1500)"
  rm -f "fwd$V.cnf"
  if [ "$e" = 0 ]; then
    kv "lrat_bytes_$V" "$(stat -c %s "fwd$V.lrat")"; kv "pog_bytes_$V" "$(stat -c %s "fwd$V.pog")"
    [ $V = A ] && kv mask_kept_A "$(tr -cd 1 < fwdA.keep | wc -c | xargs)" && kv mask_len_A "$(stat -c %s fwdA.keep)"
  fi
done
peak c2l
rm -f cert.cpog
case "$FAMILY" in
  edges) ARGP="$W/$INST.cnf" ;;
  dimacs) ARGP="$CNF" ;;
  *) ARGP="$ARG" ;;
esac
export PATH=/home1/szeider/.elan/bin:$PATH
PL="--plugin=$PLUG_LC --plugin=$PLUG_MC"
ST=""
for V in $ORDER; do
  if [ "$(grep "^c2l_exit_$V=" "$R_" | cut -d= -f2)" != 0 ]; then kv "status_$V" "c2l_failed"; ST="$ST $V:c2l"; continue; fi
  TLF=(--command); [ $V = A ] && TLF+=(--keep "$W/fwdA.keep")
  cd "$W"
  $UV run -q --no-project "$SCRIPTS/theorem_lean.py" "${TLF[@]}" "$FAMILY" "$ARGP" stream "$N" "fwd$V.pog" "fwd$V.lrat" "${DESC:-$INST}" > "T_$V.lean" \
    || { kv "status_$V" theorem_file; ST="$ST $V:thm"; continue; }
  cp "T_$V.lean" "$RESDIR/$INST.T_$V.lean"
  cd "$LEANDIR" || fin "no_leandir"
  t=$(now)
  rss "lean_$V" "$TO_LEAN" lake env lean $PL "$W/T_$V.lean" > "$W/lean_$V.out" 2>&1; e=$?
  kv "lean_exit_$V" "$e"; kv "lean_s_$V" "$(dt $t)"
  kv "stamps_$V" "$(grep '^stamp' "$W/lean_$V.out" | awk '{print $2}' | paste -sd' ')"
  CI=$(grep -m1 '^count_models' "$W/lean_$V.out" | sed 's/^count_models [^:]*: [0-9]*//')
  kv "cmd_info_$V" "$(echo "$CI" | head -c 400)"
  kv "part_b_ms_$V" "$(echo "$CI" | sed -n 's/.*part B[^,]* \([0-9]*\) ms.*/\1/p')"
  kv "part_ac_ms_$V" "$(echo "$CI" | sed -n 's/.*parts A and C \([0-9]*\) ms.*/\1/p')"
  if [ "$e" = 0 ] && grep -q "depends on axioms" "$W/lean_$V.out" && ! grep -q "error" "$W/lean_$V.out"; then
    kv "status_$V" proved; ST="$ST $V:proved"
  else
    kv "status_$V" "lean_$(why $e)"; kv "lean_out_$V" "$(grep -v '^stamp' "$W/lean_$V.out" | head -c 600 | tr '\n' ' ')"
    ST="$ST $V:lean_$(why $e)"
  fi
  rm -f "$W/fwd$V.lrat"
done
fin "$(echo $ST | tr ' ' ',')"

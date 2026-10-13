#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -J mce2e
#SBATCH -c 2
#SBATCH --mem=32G
#SBATCH -t 12:00:00
#SBATCH -o /home1/szeider/mccert/scope/logs/%x.%A.out
# Site defaults of our Slurm cluster; adjust the paths before use elsewhere.
# End-to-end theorem, the single driver of the pipeline: D4 and
# cpog-gen on the CNF, pog_count.py cross-check, the translator (native cpog2lrat from
# tools-src/cpog2lrat; PY_C2L=1: scripts/cpog2lrat.py, identical output), theorem file by
# theorem_lean.py, Lean with the precompiled checker. Results in RES/e2e_MODE.txt, ending
# with status=...
#   THM     command (default): the tool front end, `import CountCatcher` and one `count_models
#           +MODE THM via (LEMMA) "fwd.pog" "fwd.lrat" (count := N)` (dimacs: the file form),
#           N = D4's count (or the certificate's, see count_used) as a checked hint; HINT=0
#           omits the hint (the command then computes N by part A at elaboration time).
#           script: the statement typed out by theorem_lean.py (the route of the first theorem table, 2026-09-29).
#           Needs CountCatcher built in LEANDIR (lake build CountCatcher).
#   LEANDIR the Lean package (default /home1/szeider/mccert/lean); SCRIPTS the directory of
#           theorem_lean.py (default the scope directory)
#   FAMILY  domino | queens | grid | hypercube | edges | dimacs   ARG  n (edges, dimacs: none)
#   MODE    stream (default) | embed | auto (embed if the LRAT file has at most EMBED_MAX
#           bytes, default 64 MB, and is text, else stream)
#   DEL     1 (default): --delete, 0: none
#   TRIM    1 (default): --trim, only the additions in the backward cone of the empty clause
#           (native translator only; PY_C2L=1 writes all), 0: all additions
#   BIN     1: --binary, binary LRAT (default for MODE=stream; it cannot be embedded, so
#           MODE=embed rejects it and MODE=auto streams it), 0: text (default otherwise)
#   MASK    1: --keep (implies --trim), part B loads only the initial clauses that the kept
#           steps cite (fwd.keep: `count_models … (keep := …)` or `fwdCnfOfSel`; mask statistics
#           mask_kept, mask_len); default 1 for MODE=stream with TRIM=1 and the native
#           translator, else 0; MODE=embed with MASK=1 stops at once, MODE=auto streams
#   INLINE  1: --inline (implies --trim), single-use additions inlined into their consumer
#           (native translator only); default as MASK, that is on in streamed mode (measured
#           2026-10-02: 14-queens Lean 488 s to 307 s, translator 130 s to 190 s)
#   GEN     struct (default): cpog-gen's structural mode | mono: monolithic (-m) | hybrid
#           (cpog-gen-fwd -M GEN_M -W GEN_W: a node whose subgraph has tree size at most GEN_M is
#           justified by one SAT call, once the first GEN_W structural justifications made at
#           least one SAT call per 100; defaults 10000 and 100 as in scripts/gen_race.py) |
#           race: structural and GEN_RACE (hybrid, the default, as -M GEN_M without the gate, or
#           mono) at once on the job's two cores, each in its own directory and process group;
#           the first to finish successfully wins, the other is killed with its solver children
#           (fields gen_winner, gen_cores=2, gen_struct_s, gen_hybrid_s or gen_mono_s). No
#           gen_maxrss_kb in race mode.
#   GEN_BIN the generator, GEN_FL its options. Default (since 2026-10-02): cpog-gen-fwd with
#           "-F -T 500 -G" (forward implication only; long solver proofs through drat-trim;
#           proof clauses freed), also with CPOG_CHECK=1.
#   TOOLS   directory put first on PATH (d4, the generators, cadical, drat-trim, cpog2lrat,
#           cpog-check, cpog-lean-check; default /home1/szeider/mccert/tools/bin)
#   DESC    edges: doc line of the graph; dimacs: theorem name prefix (default INST)
#   CNF     the formula (default cnf/INST.cnf)                    RES    default results/INST
#   TO_D4, TO_GEN, TO_LEAN  timeouts in seconds (default 0 = none); TO_GEN also bounds
#           pog_count.py and the translator (time: c2l_s, which one: c2l_impl)
#   CPOG_CHECK=1  after our pipeline (unchanged, forward-only certificate), generate the FULL
#           certificate (reverse half included) from the same D4 output with GEN_FULL_BIN
#           (default the unpatched cpog-gen, no options; fields gen_full_s, gen_full_exit,
#           gen_full_maxrss_kb, gen_full_bytes) and run CPOG's checkers (cpog-check, the
#           Lean-verified cpog-lean-check) on it; results in RES/cpog_baseline.txt as written by
#           cpog_baseline.sbatch. The full generation and each checker get at most TO_BASE
#           seconds (default 3600), capped by the job's remaining time (WALL, default 18000 s).
#           KEEP_CERT=1 (older submissions) means the same. Both certificates are deleted;
#           certificates never leave scratch.
# Memory: mem_peak_STAGE is the job cgroup's cumulative memory.peak (earlier stages and page
# cache included); STAGE_maxrss_kb (d4, gen, c2l, lean) is the peak RSS of the largest process
# of that stage alone. Provenance: lean_commit, lratcatcher_rev, sha256 of the plugins and of the
# translator. The translator's usage text must name --trim (--keep, --inline) if TRIM (MASK,
# INLINE) is 1.
# Usage: sbatch -C genoa --mem=64G --export=ALL,INST=q13,FAMILY=queens,ARG=13 e2e.sbatch
#        sbatch --export=ALL,INST=jean,FAMILY=edges,MODE=embed,DESC="DIMACS jean" e2e.sbatch
#        sbatch --export=ALL,INST=x,FAMILY=dimacs,CNF=/path/x.cnf,MODE=auto e2e.sbatch
set -uo pipefail
S=/home1/szeider/mccert/scope
UV=/home1/szeider/.local/bin/uv
MODE=${MODE:-stream}; DEL=${DEL:-1}; ARG=${ARG:-}; THM=${THM:-command}; HINT=${HINT:-1}
TRIM=${TRIM:-1}; [ "${PY_C2L:-0}" = 1 ] && TRIM=0
GEN=${GEN:-struct}; CPOG_CHECK=${CPOG_CHECK:-${KEEP_CERT:-0}}
GEN_RACE=${GEN_RACE:-hybrid}; GEN_M=${GEN_M:-10000}; GEN_W=${GEN_W:-100}
GEN_BIN=${GEN_BIN:-cpog-gen-fwd}; GEN_FL=${GEN_FL:--F -T 500 -G}; GEN_FULL_BIN=${GEN_FULL_BIN:-cpog-gen}
BIN=${BIN:-$([ "$MODE" = stream ] && echo 1 || echo 0)}
MASK=${MASK:-$([ "$MODE" = stream ] && [ "$TRIM" = 1 ] && echo 1 || echo 0)}
[ "${PY_C2L:-0}" = 1 ] && MASK=0; [ "$MASK" = 1 ] && TRIM=1
INLINE=${INLINE:-$MASK}; [ "${PY_C2L:-0}" = 1 ] && INLINE=0; [ "$INLINE" = 1 ] && TRIM=1
LEANDIR=${LEANDIR:-/home1/szeider/mccert/lean}; SCRIPTS=${SCRIPTS:-$S}
CNF=${CNF:-$S/cnf/$INST.cnf}; RES=${RES:-$S/results/$INST}
TO_D4=${TO_D4:-0}; TO_GEN=${TO_GEN:-0}; TO_LEAN=${TO_LEAN:-0}
EMBED_MAX=${EMBED_MAX:-67108864}
TOOLS=${TOOLS:-/home1/szeider/mccert/tools/bin}
export PATH=$TOOLS:$PATH
R_=$RES/e2e_$MODE.txt; mkdir -p "$RES"; : > "$R_"
kv() { echo "$1=$2" >> "$R_"; }
now() { date +%s.%N; }
dt() { awk -v a="$1" -v b="$(now)" 'BEGIN{printf "%.1f", b-a}'; }
cg=$(cut -d: -f3 /proc/self/cgroup | head -1)
peak() { kv "mem_peak_$1" "$(cat /sys/fs/cgroup${cg}/memory.peak 2>/dev/null || echo unknown)"; }
W=${SLURM_TMPDIR:-/tmp/szeider.$SLURM_JOB_ID}/$INST; mkdir -p "$W"; cd "$W" || exit 90
# Ends the run: status, overall memory peak, scratch cleanup.
T0=$(date +%s)
# CPOG's checkers on cert.cpog (once, before cleanup). run OUT TO cmd...: wall, exit, peak RSS
# in KB of cmd (getrusage of the children; no /usr/bin/time on the compute nodes).
PYRUN='import resource, subprocess, sys, time
cmd = ["timeout", sys.argv[2]] + sys.argv[3:]
t = time.time()
with open(sys.argv[1], "w") as f:
    rc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT).returncode
print("%.1f %d %d" % (time.time() - t, rc, resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss))'
base() {
  [ "$CPOG_CHECK" = 1 ] && [ -s "$W/in.nnf" ] || return 0
  cd "$W" || return 0
  local B=$RES/cpog_baseline.txt s e m to C; : > "$B"
  bk() { echo "$1=$2" >> "$B"; }
  bk host "$(hostname)"; bk cnf "$CNF"; bk count "$N"; bk gen_s "${GEN_S:-}"
  bk fwd_cpog_bytes "${FWD_BYTES:-}"
  # the full certificate for CPOG's checkers, from the same D4 output, in its own directory
  # (cpog-gen writes temporary files into its working directory)
  to=$(( T0 + ${WALL:-18000} - 300 - $(date +%s) )); [ "$to" -gt "${TO_BASE:-3600}" ] && to=${TO_BASE:-3600}
  if [ "$to" -lt 60 ]; then bk gen_full_exit skipped_walltime; rm -f in.nnf; return 0; fi
  mkdir -p full && cd full || return 0
  read -r s e m <<< "$($UV run -q --no-project python -c "$PYRUN" gen_full.log "$to" "$GEN_FULL_BIN" ../in.cnf ../in.nnf ../cert.cpog)"
  cd "$W"; rm -f in.nnf
  bk gen_full_bin "$GEN_FULL_BIN"; bk sha256_gen_full "$(sha "$(command -v "$GEN_FULL_BIN")")"
  bk gen_full_s "$s"; bk gen_full_exit "$e"; bk gen_full_maxrss_kb "$m"; bk gen_full_timeout "$to"
  bk gen_full_bytes "$(stat -c %s cert.cpog 2>/dev/null)"
  if [ "$e" != 0 ] || [ ! -s cert.cpog ]; then
    bk gen_full_tail "$(tail -c 300 full/gen_full.log | tr '\n' ' ')"; rm -rf full cert.cpog; return 0
  fi
  rm -rf full
  bk cpog_bytes "$(stat -c %s cert.cpog)"
  for c in cc vc; do
    to=$(( T0 + ${WALL:-18000} - 300 - $(date +%s) )); [ "$to" -gt "${TO_BASE:-3600}" ] && to=${TO_BASE:-3600}
    if [ "$to" -lt 60 ]; then bk "${c}_exit" skipped_walltime; continue; fi
    if [ $c = cc ]; then read -r s e m <<< "$($UV run -q --no-project python -c "$PYRUN" cc.out "$to" cpog-check in.cnf cert.cpog)"
    else read -r s e m <<< "$($UV run -q --no-project python -c "$PYRUN" vc.out "$to" cpog-lean-check -c in.cnf cert.cpog)"; fi
    bk "${c}_s" "$s"; bk "${c}_exit" "$e"; bk "${c}_maxrss_kb" "$m"; bk "${c}_timeout" "$to"
    if [ $c = cc ]; then
      bk cc_success "$(grep -q 'FULL-PROOF SUCCESS' cc.out && echo yes || echo no)"
      C=$(grep -m1 'Regular model count = ' cc.out | sed 's/.*= *//')
    else
      bk vc_success "$(grep -q '^PROOF SUCCESSFUL' vc.out && echo yes || echo no)"
      C=$(grep -m1 '^Model count: ' vc.out | sed 's/^Model count: *//')
    fi
    bk "${c}_count" "$C"; bk "${c}_count_ok" "$([ -n "$N" ] && [ "$C" = "$N" ] && echo yes || echo no)"
    bk "${c}_tail" "$(tail -c 400 $c.out | tr '\n' ' ')"
  done
  rm -f cert.cpog
}
fin() { kv status "$1"; peak final; base; cd / && rm -rf "$W"; exit 0; }
# Classifies an exit code: 124 timeout, 137 killed (memory limit or signal), else failure.
why() { case "$1" in 124) echo timeout ;; 137) echo killed ;; *) echo "fail:$1" ;; esac; }
tmo() { if [ "$1" = 0 ]; then shift; "$@"; else timeout "$@"; fi; }
# rss NAME TO cmd...: tmo TO cmd (output and exit code pass through), then NAME_maxrss_kb, the
# peak RSS of the largest process that the stage waited for (ru_maxrss of the children, in kB
# on Linux; lean under lake env included), as the CPOG-checker baseline above measures it.
RSSPY='import resource, subprocess, sys
rc = subprocess.run(sys.argv[3:]).returncode
with open(sys.argv[1], "a") as f:
    f.write("%s_maxrss_kb=%d\n" % (sys.argv[2], resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss))
sys.exit(rc if rc >= 0 else 128 - rc)'
rss() { local n=$1 t=$2; shift 2; [ "$t" = 0 ] || set -- timeout "$t" "$@"; $UV run -q --no-project python -c "$RSSPY" "$R_" "$n" "$@"; }
sha() { if [ -f "$1" ]; then sha256sum "$1" | cut -c1-64; else echo missing; fi; }
# GEN=race: structural generation and GEN_RACE (mono: -m; hybrid: -M GEN_M, no gate, since
# the structural run covers the circuits where the hybrid does not pay) at the same time, each
# in its own directory (cpog-gen writes temporary files into its working directory) and,
# through job control, its own process group, so that the loser is killed together with its
# cadical and drat-trim children. The first run that exits 0 with a certificate wins; its
# cert.cpog and gen.log move here. Returns the winner's exit code, 124 after TO_GEN seconds,
# else the last exit code.
gen_race() {
  local t0 s0 ps pm es= em= w= e=1 m c=$GEN_RACE cfl
  case "$c" in mono) cfl=-m ;; hybrid) cfl="-M $GEN_M" ;; *) return 2 ;; esac
  t0=$(now); s0=$(date +%s)
  mkdir -p g_struct "g_$c"
  set -m
  (cd g_struct && exec $GEN_BIN $GEN_FL ../in.cnf ../in.nnf cert.cpog > gen.log 2>&1) & ps=$!
  (cd "g_$c" && exec $GEN_BIN $cfl $GEN_FL ../in.cnf ../in.nnf cert.cpog > gen.log 2>&1) & pm=$!
  set +m
  kv gen_cores 2
  while [ -z "$w" ] && { [ -z "$es" ] || [ -z "$em" ]; }; do
    if [ -z "$es" ] && ! kill -0 $ps 2>/dev/null; then
      wait $ps; es=$?; kv gen_struct_exit "$es"; kv gen_struct_s "$(dt $t0)"; e=$es
      [ "$es" = 0 ] && [ -s g_struct/cert.cpog ] && w=struct
    fi
    if [ -z "$w" ] && [ -z "$em" ] && ! kill -0 $pm 2>/dev/null; then
      wait $pm; em=$?; kv "gen_${c}_exit" "$em"; kv "gen_${c}_s" "$(dt $t0)"; e=$em
      [ "$em" = 0 ] && [ -s "g_$c/cert.cpog" ] && w=$c
    fi
    if [ -z "$w" ] && [ "$TO_GEN" != 0 ] && [ $(( $(date +%s) - s0 )) -ge "$TO_GEN" ]; then e=124; break; fi
    [ -n "$w" ] || sleep 0.2
  done
  for m in "$ps:$es" "$pm:$em"; do
    [ -n "${m#*:}" ] && continue
    kill -TERM -- "-${m%:*}" 2>/dev/null
    for _ in 1 2 3 4 5 6 7 8 9 10; do kill -0 "${m%:*}" 2>/dev/null || break; sleep 0.1; done
    kill -KILL -- "-${m%:*}" 2>/dev/null; wait "${m%:*}" 2>/dev/null
  done
  kv gen_winner "${w:-none}"
  if [ -n "$w" ]; then mv "g_$w/cert.cpog" "g_$w/gen.log" .; e=0
  else cp g_struct/gen.log gen.log 2>/dev/null; fi
  rm -rf g_struct "g_$c"
  return $e
}
kv host "$(hostname)"; kv cpu "$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs)"
kv affinity "$(taskset -cp $$ | cut -d: -f2 | xargs)"
kv family "$FAMILY $ARG $MODE del=$DEL trim=$TRIM bin=$BIN mask=$MASK inline=$INLINE thm=$THM hint=$HINT"
[ "$MODE" = embed ] && [ "$BIN" = 1 ] && fin "bin_embed"
[ "$MASK" = 1 ] && [ "$MODE" = embed ] && fin "mask_embed"
# The hybrid needs cpog-gen-fwd's -M (an older generator stops at the unknown option)
if [ "$GEN" = hybrid ] || { [ "$GEN" = race ] && [ "$GEN_RACE" = hybrid ]; }; then
  $GEN_BIN -h 2>&1 | grep -q -- '-M NODES' || fin "gen_lacks_hybrid"
fi
kv leandir "$LEANDIR"
# Provenance: Lean sources (git commit, -dirty with local changes, unknown without git),
# lrat-catcher revision, sha256 of the two plugins and of the translator.
kv lean_commit "$(git -C "$LEANDIR" rev-parse HEAD 2>/dev/null || echo unknown)$(git -C "$LEANDIR" status --porcelain -- . 2>/dev/null | grep -q . && echo -dirty)"
kv lratcatcher_rev "$($UV run -q --no-project python -c 'import json, sys
print(next(p["rev"] for p in json.load(open(sys.argv[1]))["packages"] if p["name"] == "LRATCatcher"))' "$LEANDIR/lake-manifest.json" 2>/dev/null || echo unknown)"
L=$LEANDIR/.lake
PLUG_LC=$L/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.so
PLUG_MC=$L/build/lib/libCountCatcher_CountCatcherChecker.so
kv sha256_plugin_lratcatcher "$(sha "$PLUG_LC")"; kv sha256_plugin_countcatcher "$(sha "$PLUG_MC")"
if [ "${PY_C2L:-0}" = 1 ]; then TRB=$SCRIPTS/cpog2lrat.py; else TRB=$(command -v cpog2lrat); fi
kv translator "$TRB"; kv sha256_translator "$(sha "$TRB")"
kv tools "$TOOLS"; kv gen_bin "$(command -v "$GEN_BIN")"; kv sha256_gen "$(sha "$(command -v "$GEN_BIN")")"
# Guard: an older translator ignores options it does not know (untrimmed output, no error).
if [ "${PY_C2L:-0}" != 1 ]; then
  U=$(cpog2lrat 2>&1)
  [ "$TRIM" = 1 ] && [[ $U != *--trim* ]] && fin "c2l_lacks_trim"
  [ "$MASK" = 1 ] && [[ $U != *--keep* ]] && fin "c2l_lacks_keep"
  [ "$INLINE" = 1 ] && [[ $U != *--inline* ]] && fin "c2l_lacks_inline"
fi
kv scratch_free "$(df -hP . | tail -1 | awk '{print $4}')"
# Guard: certificates of several GB per task; SCRATCH_MIN GB (default 100) must be free.
[ "$(df -BG -P . | tail -1 | awk '{print $4+0}')" -ge "${SCRATCH_MIN:-100}" ] || fin "infra_scratch"
kv cnf "$CNF"
cp "$CNF" in.cnf || fin "no_cnf"
kv vars "$(awk '/^p cnf/{print $3; exit}' in.cnf)"; kv clauses "$(awk '/^p cnf/{print $4; exit}' in.cnf)"
[ "$FAMILY" = edges ] && cp "$CNF" "$INST.cnf" && cp "${CNF%.cnf}.edges" "$INST.edges"
t=$(now); rss d4 "$TO_D4" d4 in.cnf -dDNNF -out=in.nnf > d4.log 2>&1; e=$?
kv d4_exit "$e"; kv d4_s "$(dt $t)"; peak d4
N=$(grep -m1 '^s ' d4.log | awk '{print $2}'); kv count "$N"
[ "$e" = 0 ] && [ -n "$N" ] && [ -s in.nnf ] || fin "d4_$(why $e)"
kv gen_mode "$GEN $GEN_BIN $GEN_FL m=$GEN_M w=$GEN_W race=$GEN_RACE"
t=$(now)
case "$GEN" in
  struct) rss gen "$TO_GEN" $GEN_BIN $GEN_FL in.cnf in.nnf cert.cpog > gen.log 2>&1; e=$? ;;
  mono) rss gen "$TO_GEN" $GEN_BIN -m $GEN_FL in.cnf in.nnf cert.cpog > gen.log 2>&1; e=$? ;;
  hybrid) rss gen "$TO_GEN" $GEN_BIN -M "$GEN_M" -W "$GEN_W" $GEN_FL in.cnf in.nnf cert.cpog > gen.log 2>&1; e=$? ;;
  race) gen_race; e=$? ;;
  *) fin "bad_gen_$GEN" ;;
esac
GEN_S=$(dt $t); kv gen_exit "$e"; kv gen_s "$GEN_S"; peak gen
# POG size as in the CPOG paper (defining clauses), printed before proof generation starts
kv pog_defs "$(grep -m1 'Compressed POG has' gen.log | sed 's/.* and \([0-9]*\) defining clauses.*/\1/')"
FWD_BYTES=$(stat -c %s cert.cpog 2>/dev/null); kv cpog_bytes "$FWD_BYTES"
[ "$CPOG_CHECK" = 1 ] || rm -f in.nnf   # CPOG_CHECK=1: the full generation needs it
if [ "$e" != 0 ]; then kv gen_tail "$(tail -c 300 gen.log | tr '\n' ' ')"; rm -f cert.cpog; fin "gen_$(why $e)"; fi
t=$(now); tmo "$TO_GEN" $UV run -q --no-project "$SCRIPTS/pog_count.py" in.cnf cert.cpog > pc.txt 2>&1; e=$?
PC=$(head -c 100000 pc.txt)
kv pog_count_ok "$([ "$PC" = "$N" ] && echo yes || echo "no:$(why $e):$(head -c 200 pc.txt)")"
kv pog_count_s "$(dt $t)"; peak pog_count
# D4's count is the claimed count; if the certificate's own count differs, the theorem states
# the certificate's count (the checker decides) and the mismatch stays in pog_count_ok.
[ "$PC" != "$N" ] && [[ "$PC" =~ ^[0-9]+$ ]] && N=$PC && kv count_used "$N"
t=$(now)
FL=""; [ "$DEL" = 1 ] && FL="--delete"; [ "$BIN" = 1 ] && FL="$FL --binary"
[ "$TRIM" = 1 ] && FL="$FL --trim"; [ "$MASK" = 1 ] && FL="$FL --keep"
[ "$INLINE" = 1 ] && FL="$FL --inline"
if [ "${PY_C2L:-0}" = 1 ]; then
  kv c2l_impl python
  rss c2l "$TO_GEN" $UV run -q --no-project "$SCRIPTS/cpog2lrat.py" in.cnf cert.cpog fwd $FL >> "$R_" 2>&1; e=$?
else
  kv c2l_impl native
  rss c2l "$TO_GEN" cpog2lrat in.cnf cert.cpog fwd $FL >> "$R_" 2>&1; e=$?
fi
kv c2l_exit "$e"; kv c2l_s "$(dt $t)"; peak c2l
rm -f fwd.cnf cert.cpog
[ "$e" = 0 ] || fin "c2l_$(why $e)"
LB=$(stat -c %s fwd.lrat); kv lrat_bytes "$LB"; kv pog_bytes "$(stat -c %s fwd.pog)"
[ "$MASK" = 1 ] && kv mask_kept "$(tr -cd 1 < fwd.keep | wc -c | xargs)" && kv mask_len "$(stat -c %s fwd.keep)"
if [ "$MODE" = auto ]; then M=stream; [ "$BIN" != 1 ] && [ "$MASK" != 1 ] && [ "$LB" -le "$EMBED_MAX" ] && M=embed; else M=$MODE; fi
kv mode "$M"
case "$FAMILY" in
  edges) ARGP="$W/$INST.cnf" ;;
  dimacs) ARGP="$CNF" ;;
  *) ARGP="$ARG" ;;
esac
TLF=(); HN=$N
if [ "$THM" = command ]; then TLF=(--command); [ "$HINT" = 0 ] && HN=-; fi
[ "$MASK" = 1 ] && TLF+=(--keep "$W/fwd.keep")
$UV run -q --no-project "$SCRIPTS/theorem_lean.py" "${TLF[@]}" "$FAMILY" "$ARGP" "$M" "$HN" fwd.pog fwd.lrat "${DESC:-$INST}" > T.lean || fin "theorem_file"
cp T.lean "$RES/T_$M.lean"
cd "$LEANDIR" || fin "no_leandir"
export PATH=/home1/szeider/.elan/bin:$PATH
# Load the precompiled checker so that native_decide runs parts A and C as native code
# (interpreted, the Q_6 theorem took 72 s instead of 17 s on the Mac). The same two plugins
# serve THM=command: the command's own code (CountCatcherMath.Command, not precompiled) only
# elaborates and calls the checker, which runs from the CountCatcherChecker plugin.
PL="--plugin=$PLUG_LC --plugin=$PLUG_MC"
t=$(now)
rss lean "$TO_LEAN" lake env lean $PL "$W/T.lean" > "$W/lean.out" 2>&1; e=$?
kv lean_exit "$e"; kv lean_s "$(dt $t)"; peak lean
kv stamps "$(grep '^stamp' "$W/lean.out" | awk '{print $2}' | paste -sd' ')"
kv cmd_info "$(grep -m1 '^count_models' "$W/lean.out" | head -c 400)"
# the verified evaluations' times (cmd_info is cut at 400 bytes, which drops them after a long count)
CI=$(grep -m1 '^count_models' "$W/lean.out" | sed 's/^count_models [^:]*: [0-9]*//')
kv part_b_ms "$(echo "$CI" | sed -n 's/.*part B[^,]* \([0-9]*\) ms.*/\1/p')"
kv part_ac_ms "$(echo "$CI" | sed -n 's/.*parts A and C \([0-9]*\) ms.*/\1/p')"
kv part_abc_ms "$(echo "$CI" | sed -n 's/.*(parts A, B, C) \([0-9]*\) ms.*/\1/p')"
kv lean_out "$(grep -v '^stamp' "$W/lean.out" | head -c 800 | tr '\n' ' ')"
if [ "$e" = 0 ] && grep -q "depends on axioms" "$W/lean.out" && ! grep -q "error" "$W/lean.out"; then
  fin proved
fi
fin "lean_$(why $e)"

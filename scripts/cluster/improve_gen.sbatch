#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -C genoa
#SBATCH -J ovngen
#SBATCH -c 2
#SBATCH --mem=32G
#SBATCH -t 03:00:00
#SBATCH -o /home1/szeider/mccert/ovn/logs/%x.%j.out
# Site defaults of our Slurm cluster; adjust the paths before use elsewhere.
# Before/after measurements of translator and checker variants, job type G: the certificate of
# one instance, kept on slurm-cpu01's node-local scratch (hence -C genoa for every job) so that
# later variants run on the same certificate (improve_check.sbatch).
#   INSTANCE  CNF /home1/szeider/mccert/ovn/cnf/INSTANCE.cnf (env CNF overrides)
#   directory /scratch/szeider/mccert_ovn/INSTANCE/: in.cnf, in.nnf (D4 -dDNNF), cert.cpog
#             (cpog-gen-norev -F), d4.log, gen.log, gen.txt (copy of the result), gen.done
#             (the count the checks use)
# If gen.done exists, nothing is done (exit 0). Stages: D4 (timeout TO_D4, default 3600 s),
# cpog-gen-norev -F (TO_GEN, 9000 s), pog_count.py cross-check (TO_PC, 1800 s; a timeout is
# recorded, not fatal). Each stage: wall s, CPU s, peak RSS, exit (improve_stage.py). As in
# e2e.sbatch, the certificate's count replaces D4's if they differ (pog_count_ok records it).
# REF: optional reference count (ref_ok=yes|no). Result: ovn/results/INSTANCE.gen.txt.
# GENTAG (default empty) and GENFLAGS (default -F): a second certificate of the same instance,
# e.g. GENTAG=_m GENFLAGS="-m -F" (monolithic mode) writes cert_m.cpog, gen_m.log, gen_m.done,
# gen_m.txt and ovn/results/INSTANCE.gen_m.txt; it reuses in.nnf and D4's count of the default
# run, which must have finished (gen.done), and does not run D4 again. MONO=1 sets GENFLAGS to
# "-m -F" (for sbatch --export, where a value with a space is awkward). GENBIN (default
# cpog-gen-norev) is the generator; FWD=1 sets GENBIN to tools_ovn/fwd/cpog-gen-fwd (51dfbb5's
# cpog-gen-fwd.patch) and GENFLAGS to "-F -T 500 -G".
# Exit 0 iff the certificate is complete, so check jobs can follow with --dependency=afterok.
# Usage: sbatch [--mem=64G] [-J ovnL3 --dependency=singleton] [--export=ALL,REF=73712] \
#          /home1/szeider/mccert/ovn/scripts/improve_gen.sbatch q13
set -uo pipefail
INST=${1:?usage: improve_gen.sbatch INSTANCE}
O=/home1/szeider/mccert/ovn
CNF=${CNF:-$O/cnf/$INST.cnf}
D=/scratch/szeider/mccert_ovn/$INST
GT=${GENTAG:-}; GF=${GENFLAGS:--F}; [ "${MONO:-0}" = 1 ] && GF="-m -F"
GB=${GENBIN:-cpog-gen-norev}
[ "${FWD:-0}" = 1 ] && GB=/home1/szeider/mccert/tools_ovn/fwd/cpog-gen-fwd && GF="-F -T 500 -G"
R=$O/results/$INST.gen$GT.txt
SCRIPTS=${SCRIPTS:-$O/src_base/scripts}
TB=/home1/szeider/mccert/tools/bin
export PATH=$TB:$PATH   # cpog-gen calls cadical and drat-trim by name
PY=$(command -v python3 || echo "/home1/szeider/.local/bin/uv run -q --no-project python")
STAGE="$PY $O/scripts/improve_stage.py"
mkdir -p "$D" "$O/results" || exit 2
exec 9> "$D/.gen$GT.lock"
flock -n 9 || { echo "busy: another generation job holds $D ($GT)"; exit 3; }
if [ -s "$D/gen$GT.done" ] && [ -s "$D/cert$GT.cpog" ]; then echo "cached: $D/gen$GT.done"; exit 0; fi
if [ -n "$GT" ] && ! { [ -s "$D/gen.done" ] && [ -s "$D/in.nnf" ]; }; then
  echo "GENTAG=$GT needs the default run's in.nnf and gen.done in $D"; exit 4
fi
cd "$D" || exit 2
if [ -z "$GT" ]; then rm -f in.nnf cert.cpog gen.done gen.txt d4.log gen.log pc.txt reduction-*
else rm -f "cert$GT.cpog" "gen$GT.done" "gen$GT.txt" "gen$GT.log" "pc$GT.txt"; fi
: > "$R"
kv() { echo "$1=$2" >> "$R"; }
fin() {
  kv status "$1"; kv uptime_end "$(uptime)"
  local cg; cg=$(cut -d: -f3 /proc/self/cgroup | head -1)
  kv mem_peak_job "$(cat /sys/fs/cgroup${cg}/memory.peak 2>/dev/null || echo unknown)"
  cp "$R" "$D/gen$GT.txt"
  [ -n "${SLURM_TMPDIR:-}" ] && rmdir "$SLURM_TMPDIR" 2>/dev/null
  [ "$1" = generated ] && exit 0
  rm -f "cert$GT.cpog"; exit 1
}
kv inst "$INST"; kv gentag "$GT"; kv genbin "$GB"; kv genflags "$GF"; kv job "${SLURM_JOB_ID:-none}"; kv host "$(hostname)"
kv uptime_start "$(uptime)"; kv date "$(date -Is)"
kv cpu "$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs)"
kv affinity "$(taskset -cp $$ | cut -d: -f2 | xargs)"; kv mem_limit_mb "${SLURM_MEM_PER_NODE:-unknown}"
kv python "$PY"
for t in d4 cpog-gen-norev cadical drat-trim; do
  kv "sha256_$t" "$(sha256sum "$(readlink -f "$TB/$t")" | cut -d' ' -f1)"
done
kv sha256_genbin "$(sha256sum "$(command -v "$GB")" | cut -d' ' -f1)"
FREE=$(df -BG -P "$D" | tail -1 | awk '{print $4+0}'); kv scratch_free_gb "$FREE"
[ "$FREE" -ge "${SCRATCH_MIN:-100}" ] || fin infra_scratch
if [ -z "$GT" ]; then
  cp "$CNF" in.cnf || fin no_cnf
  kv cnf "$CNF"; kv cnf_sha256 "$(sha256sum in.cnf | cut -d' ' -f1)"
  kv vars "$(awk '/^p cnf/{print $3; exit}' in.cnf)"; kv clauses "$(awk '/^p cnf/{print $4; exit}' in.cnf)"
  $STAGE "$R" d4 "${TO_D4:-3600}" d4.log d4 in.cnf -dDNNF -out=in.nnf; e=$?
  N=$(grep -m1 '^s ' d4.log | awk '{print $2}'); kv count_d4 "$N"
  [ "$e" = 0 ] && [ -n "$N" ] && [ -s in.nnf ] || fin "d4_fail:$e"
else
  kv cnf_sha256 "$(sha256sum in.cnf | cut -d' ' -f1)"; kv d4_reused yes
  N=$(grep -m1 '^s ' d4.log | awk '{print $2}'); kv count_d4 "$N"
  [ -n "$N" ] || fin no_d4_count
fi
kv nnf_bytes "$(stat -c %s in.nnf)"
# shellcheck disable=SC2086
$STAGE "$R" gen "${TO_GEN:-9000}" "gen$GT.log" "$GB" $GF in.cnf in.nnf "cert$GT.cpog"; e=$?
kv pog_nodes "$(grep -m1 'Compressed POG has' "gen$GT.log" | sed 's/.*has \([0-9]*\) nodes.*/\1/')"
kv pog_defs "$(grep -m1 'Compressed POG has' "gen$GT.log" | sed 's/.* and \([0-9]*\) defining clauses.*/\1/')"
kv cpog_bytes "$(stat -c %s "cert$GT.cpog" 2>/dev/null)"
if [ "$e" != 0 ]; then kv gen_tail "$(tail -c 300 "gen$GT.log" | tr '\n' ' ')"; fin "gen_fail:$e"; fi
$STAGE "$R" pog_count "${TO_PC:-1800}" "pc$GT.txt" $PY "$SCRIPTS/pog_count.py" in.cnf "cert$GT.cpog"; e=$?
PC=$(head -c 100000 "pc$GT.txt")
if [ "$PC" = "$N" ]; then kv pog_count_ok yes
elif [ "$e" = 124 ]; then kv pog_count_ok timeout
else kv pog_count_ok "no:$e:$(head -c 200 pc.txt | tr '\n' ' ')"; fi
NU=$N
[ "$PC" != "$N" ] && [[ "$PC" =~ ^[0-9]+$ ]] && NU=$PC && kv count_used_from cert
kv count "$NU"
[ -n "${REF:-}" ] && kv ref_ok "$([ "$REF" = "$NU" ] && echo yes || echo "no:$REF")"
echo "$NU" > "gen$GT.done"
fin generated

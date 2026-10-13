#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -J tdpog
#SBATCH -c 2
#SBATCH --mem=32G
#SBATCH -t 06:00:00
#SBATCH -o /home1/szeider/mccert/td/logs/%x.%j.out
# Site defaults of our Slurm cluster; adjust the paths before use elsewhere.
# Phase 1 of the part C comparison: the POG of one instance (D4, cpog-gen-norev -F,
# native cpog2lrat) in $SLURM_TMPDIR, copied with its CNF to td/pog/INST.{pog,cnf};
# provenance in td/pog/INST.gen.txt. Phase 2: td_time.sbatch.
# Usage: sbatch --export=ALL,INST=x,CNF=/path/x.cnf [--mem=…] [-C nvme] td_pog.sbatch
set -uo pipefail
TD=/home1/szeider/mccert/td
mkdir -p "$TD/pog"; OUT=$TD/pog/$INST.gen.txt; : > "$OUT"
export PATH=/home1/szeider/mccert/tools/bin:$PATH
kv() { echo "$1=$2" >> "$OUT"; }
now() { date +%s.%N; }
dt() { awk -v a="$1" -v b="$(now)" 'BEGIN{printf "%.1f", b-a}'; }
W=${SLURM_TMPDIR:-/tmp/szeider.$SLURM_JOB_ID}/tdpog_$INST; mkdir -p "$W"; cd "$W" || exit 90
kv host "$(hostname)"; kv cpu "$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs)"
kv job "$SLURM_JOB_ID"; kv cnf "$CNF"; kv scratch_free "$(df -hP . | tail -1 | awk '{print $4}')"
cp "$CNF" in.cnf || { kv status no_cnf; exit 0; }
t=$(now); d4 in.cnf -dDNNF -out=in.nnf > d4.log 2>&1; kv d4_exit $?; kv d4_s "$(dt $t)"
kv count "$(grep -m1 '^s ' d4.log | awk '{print $2}')"
t=$(now); cpog-gen-norev -F in.cnf in.nnf cert.cpog > gen.log 2>&1; e=$?
kv gen_exit $e; kv gen_s "$(dt $t)"; rm -f in.nnf
kv cpog_bytes "$(stat -c %s cert.cpog 2>/dev/null)"
[ $e = 0 ] || { kv gen_tail "$(tail -c 300 gen.log | tr '\n' ' ')"; kv status gen_failed; cd / && rm -rf "$W"; exit 1; }
t=$(now); cpog2lrat in.cnf cert.cpog fwd > c2l.log 2>&1; e=$?; kv c2l_exit $e; kv c2l_s "$(dt $t)"
rm -f fwd.lrat fwd.cnf cert.cpog
[ $e = 0 ] && [ -s fwd.pog ] || { kv status c2l_failed; cd / && rm -rf "$W"; exit 1; }
kv pog_bytes "$(stat -c %s fwd.pog)"
cp fwd.pog "$TD/pog/$INST.pog" && cp in.cnf "$TD/pog/$INST.cnf" || { kv status copy_failed; exit 1; }
kv status done
cd / && rm -rf "$W"

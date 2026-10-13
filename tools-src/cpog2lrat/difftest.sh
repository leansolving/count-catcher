#!/bin/bash
# Differential test: scripts/cpog2lrat.py against the native cpog2lrat on one CNF and CPOG
# pair, for the option combinations none, --delete, --binary, --delete --binary. Compares
# exit code, stdout, stderr (only whether it is empty) and OUT.pog, OUT.cnf, OUT.lrat byte
# by byte, and checks that no temporary file is left.
# Then --trim and --keep, which the Python translator lacks: the native translator with the
# same four combinations against scripts/lrat_trim.py applied to the Python translator's
# untrimmed outputs. Compares exit code, OUT.pog (equal to the Python one), OUT.cnf (--trim:
# the Python one; --keep: the reference's kept clauses), OUT.keep (--keep), OUT.lrat byte by
# byte, stdout (the Python line, with deleted=K of the reference for --delete) and the
# statistics lines (native stderr, reference stdout). With LRAT_CHECK set to drat-trim's
# lrat-check, every text OUT.lrat is also checked against OUT.cnf ("lrat_check=ok").
# Then --inline and --inline --keep, in the same four combinations, against the reference
# pipeline: scripts/lrat_trim.py (with --keep if given) on the Python translator's untrimmed
# output, text without deletions, then scripts/lrat_inline.py (default window) with the
# combination's --delete and --binary on it (OUT.cnf: the Python one, or with --keep the
# reference's kept clauses). The statistics lines are the trim (and keep) lines of
# lrat_trim.py and the inline line of lrat_inline.py; the native inline line is compared
# without its fifo_peak field and what follows it.
# One result line per combination: "NAME FLAGS identical|DIFF ...", plus Python and native
# wall seconds.
# Usage: difftest.sh NAME CNF CPOG WORKDIR [PY_SCRIPT] [NATIVE_BIN] [TRIM_REF] [INLINE_REF]
set -uo pipefail
NAME=$1; CNF=$2; CPOG=$3; W=$4
D=$(cd "$(dirname "$0")" && pwd)
PY=${5:-$D/../../scripts/cpog2lrat.py}
NB=${6:-$D/../../tools/bin/cpog2lrat}
TR=${7:-$D/../../scripts/lrat_trim.py}
IR=${8:-$D/../../scripts/lrat_inline.py}
UV=${UV:-uv}
mkdir -p "$W"
now() { date +%s.%N; }
for FL in "" "--delete" "--binary" "--delete --binary"; do
  rm -rf "$W/py" "$W/nat"; mkdir -p "$W/py" "$W/nat"
  t=$(now)
  # shellcheck disable=SC2086
  $UV run -q --no-project "$PY" "$CNF" "$CPOG" "$W/py/fwd" $FL > "$W/py.out" 2> "$W/py.err"; ep=$?
  tp=$(awk -v a="$t" -v b="$(now)" 'BEGIN{printf "%.2f", b-a}')
  t=$(now)
  # shellcheck disable=SC2086
  "$NB" "$CNF" "$CPOG" "$W/nat/fwd" $FL > "$W/nat.out" 2> "$W/nat.err"; en=$?
  tn=$(awk -v a="$t" -v b="$(now)" 'BEGIN{printf "%.2f", b-a}')
  bad=""
  [ "$ep" = "$en" ] || bad="$bad exit($ep,$en)"
  cmp -s "$W/py.out" "$W/nat.out" || bad="$bad stdout"
  { [ -s "$W/py.err" ] && [ -s "$W/nat.err" ]; } || { [ ! -s "$W/py.err" ] && [ ! -s "$W/nat.err" ]; } \
    || bad="$bad stderr"
  if [ "$ep" = 0 ]; then
    for f in pog cnf lrat; do cmp -s "$W/py/fwd.$f" "$W/nat/fwd.$f" || bad="$bad fwd.$f"; done
    [ "$(ls "$W/py")" = "$(ls "$W/nat")" ] || bad="$bad files($(ls "$W/py" | tr '\n' ,)|$(ls "$W/nat" | tr '\n' ,))"
    sz=$(stat -c %s "$W/nat/fwd.lrat" 2>/dev/null || stat -f %z "$W/nat/fwd.lrat")
  else
    sz="-"
    bad="$bad [error py: $(head -c 150 "$W/py.err" | tail -1 | tr '\n' ' ') | native: $(head -c 150 "$W/nat.err" | tr '\n' ' ')]"
    [ "$ep" = "$en" ] && bad="${bad# }" && bad="both-fail $bad"
  fi
  res=${bad:-identical}
  echo "$NAME [${FL:-none}] $res py_s=$tp nat_s=$tn lrat_bytes=$sz stdout=$(tr '\n' ' ' < "$W/nat.out")"
done
rm -rf "$W/py" "$W/nat"; mkdir -p "$W/py"
$UV run -q --no-project "$PY" "$CNF" "$CPOG" "$W/py/fwd" > "$W/py.out" 2> "$W/py.err"; ep=$?
for TM in --trim --keep --inline "--inline --keep"; do
for FL in "" "--delete" "--binary" "--delete --binary"; do
  rm -rf "$W/nat" "$W"/ref.* "$W"/reft.*; mkdir -p "$W/nat"
  t=$(now)
  # shellcheck disable=SC2086
  "$NB" "$CNF" "$CPOG" "$W/nat/fwd" $TM $FL > "$W/nat.out" 2> "$W/nat.err"; en=$?
  tn=$(awk -v a="$t" -v b="$(now)" 'BEGIN{printf "%.2f", b-a}')
  bad=""; chk=""
  [ "$ep" = "$en" ] || bad="$bad exit($ep,$en)"
  if [ "$ep" = 0 ] && [ "$en" = 0 ]; then
    KF=""; case "$TM" in *--keep*) KF=--keep ;; esac
    RC=$W/ref.cnf; RK=$W/ref.keep
    case "$TM" in
      --inline*)
        # shellcheck disable=SC2086
        $UV run -q --no-project "$TR" "$CNF" "$W/py/fwd.lrat" "$W/reft.lrat" $KF > "$W/ref.out" 2>&1 \
          || bad="$bad reference_failed"
        IC=$W/py/fwd.cnf; [ -n "$KF" ] && IC=$W/reft.cnf
        RC=$W/reft.cnf; RK=$W/reft.keep
        # shellcheck disable=SC2086
        $UV run -q --no-project "$IR" "$IC" "$W/reft.lrat" "$W/ref.lrat" $FL >> "$W/ref.out" 2>&1 \
          || bad="$bad reference_failed" ;;
      *)
        # shellcheck disable=SC2086
        $UV run -q --no-project "$TR" "$CNF" "$W/py/fwd.lrat" "$W/ref.lrat" $FL $KF > "$W/ref.out" 2>&1 \
          || bad="$bad reference_failed" ;;
    esac
    exp=$(cat "$W/py.out")
    case "$FL" in *delete*)
      k=$(sed -n 's/^deleted=//p' "$W/ref.out")
      exp=$(sed "s/\(additions=[0-9]*\)/\1 deleted=$k/" "$W/py.out") ;;
    esac
    [ "$exp" = "$(cat "$W/nat.out")" ] || bad="$bad stdout"
    [ "$(grep -v '^deleted=' "$W/ref.out")" = "$(sed 's/ fifo_peak=.*//' "$W/nat.err")" ] \
      || bad="$bad stats"
    cmp -s "$W/py/fwd.pog" "$W/nat/fwd.pog" || bad="$bad fwd.pog"
    if [ -n "$KF" ]; then
      cmp -s "$RC" "$W/nat/fwd.cnf" || bad="$bad fwd.cnf"
      cmp -s "$RK" "$W/nat/fwd.keep" || bad="$bad fwd.keep"
      files=$(printf 'fwd.cnf\nfwd.keep\nfwd.lrat\nfwd.pog')
    else
      cmp -s "$W/py/fwd.cnf" "$W/nat/fwd.cnf" || bad="$bad fwd.cnf"
      files=$(printf 'fwd.cnf\nfwd.lrat\nfwd.pog')
    fi
    cmp -s "$W/ref.lrat" "$W/nat/fwd.lrat" || bad="$bad fwd.lrat"
    [ "$(ls "$W/nat")" = "$files" ] || bad="$bad files($(ls "$W/nat" | tr '\n' ,))"
    sz=$(stat -c %s "$W/nat/fwd.lrat" 2>/dev/null || stat -f %z "$W/nat/fwd.lrat")
    case "$FL" in *binary*) ;; *)
      if [ -n "${LRAT_CHECK:-}" ]; then
        "$LRAT_CHECK" "$W/nat/fwd.cnf" "$W/nat/fwd.lrat" > "$W/lc.out" 2>&1
        if grep -q '^c VERIFIED' "$W/lc.out"; then chk=" lrat_check=ok"; else chk=" lrat_check=FAIL"; bad="$bad lrat_check"; fi
      fi ;;
    esac
  else
    sz="-"
    cmp -s "$W/py.out" "$W/nat.out" || bad="$bad stdout"
    [ -s "$W/py.err" ] && [ -s "$W/nat.err" ] || bad="$bad stderr"
    bad="$bad [error py: $(head -c 150 "$W/py.err" | tail -1 | tr '\n' ' ') | native: $(head -c 150 "$W/nat.err" | tr '\n' ' ')]"
    [ "$ep" = "$en" ] && bad="${bad# }" && bad="both-fail $bad"
  fi
  res=${bad:-identical}
  echo "$NAME [$TM${FL:+ $FL}] $res$chk nat_s=$tn lrat_bytes=$sz stats=$(tr '\n' ' ' < "$W/nat.err")"
done
done
rm -rf "$W/py" "$W/nat" "$W"/ref.* "$W"/reft.*

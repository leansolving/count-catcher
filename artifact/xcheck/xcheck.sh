#!/usr/bin/env bash
# count-catcher: cross-check of counts with two independent exact counters (Section 6: the four
# OEIS values; Section A.3: the five graphs of the validation families), GANAK in deterministic
# mode and sharpSAT-TD, at the commits of artifact/xcheck/counters.tsv. The counters are not
# shipped; build them from those commits and point the script at the binaries:
#
#   GANAK=/path/to/ganak SHARPSAT_DIR=/path/to/sharpsat-td/bin artifact/xcheck/xcheck.sh [OUT]
#
# SHARPSAT_DIR holds sharpSAT and flow_cutter_pace17 (sharpSAT runs ./flow_cutter_pace17, so it
# runs in that directory). The inputs are regenerated: the four OEIS formulas exported from the
# Lean encoders with #export_cnf (the formulas of the theorems; same clauses as the files the
# paper's runs used), the five graphs by scripts/gen_t5.py; comment lines are dropped, and every
# count is compared with artifact/xcheck/expected.tsv. Needs the installation (artifact/install.sh). Output in OUT (default artifact/out/xcheck): NAME.cnf,
# NAME.ganak.out, NAME.sstd.out, result.tsv (name, counter, exit, seconds, count, verdict).
# TO (default 3600) limits each run in seconds; SSTD_CACHE_MB (default 3500) is sharpSAT-TD's
# cache. About 4 minutes (208 s on a 2016 Xeon E5-2640 v4, with the Lean export; one counter run at a time).
# The outputs of the paper's runs are in artifact/xcheck/runs/2026-10-01_oeis and 2026-10-09_graphs, those
# of this script (2026-10-11, all 18 PASS, ganak --prob 0, exit 0 everywhere) in runs/2026-10-11_xcheck.
set -uo pipefail
ROOT=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")/../.." && pwd)
# shellcheck source=/dev/null
source "$ROOT/artifact/env.sh"
: "${GANAK:?set GANAK to the ganak binary}" "${SHARPSAT_DIR:?set SHARPSAT_DIR to the bin directory of sharpSAT-TD}"
OUT=$(mkdir -p "${1:-$ROOT/artifact/out/xcheck}" && cd "${1:-$ROOT/artifact/out/xcheck}" && pwd)
TO=${TO:-3600}; CS=${SSTD_CACHE_MB:-3500}
X=$ROOT/artifact/xcheck
cd "$ROOT" || exit 2
EXT=so; [ "$(uname)" = Darwin ] && EXT=dylib
L=$ROOT/lean/.lake
export_oeis() {  # the four OEIS formulas from the Lean encoders, one Lean run
  {
    echo 'import CountCatcher'
    echo '#export_cnf via (CountCatcher.Kreweras.card_of_check (n := 6)) "A358391_6.raw"'
    echo '#export_cnf via (CountCatcher.Sperner.card_of_check (n := 7)) "A396728_7.raw"'
    echo '#export_cnf via (CountCatcher.TotalDom.torus_card_of_check (m := 7)) "A303210_9.raw"'
    echo '#export_cnf via (CountCatcher.TotalDom.torus_card_of_check (m := 8)) "A303210_10.raw"'
  } > "$OUT/export.lean"
  (cd "$ROOT/lean" && lake env lean \
     "--plugin=$L/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.$EXT" \
     "--plugin=$L/build/lib/libCountCatcher_CountCatcherChecker.$EXT" "$OUT/export.lean") \
     > "$OUT/export.out" 2>&1
}
gen() {  # NAME: write OUT/NAME.cnf without comment lines
  local n=$1 raw=$OUT/$1.raw
  mkdir -p "$OUT/g"
  case $n in
    A*) [ -s "$raw" ] || export_oeis ;;
    hq6) uv run --no-project -q scripts/gen_t5.py "$OUT/g" hq6 hypercube 6 && cp "$OUT/g/hq6.cnf" "$raw" ;;
    cub*) uv run --no-project -q scripts/gen_t5.py "$OUT/g" "$n" cubic "${n#cub}" 1 && cp "$OUT/g/$n.cnf" "$raw" ;;
    *) uv run --no-project -q scripts/gen_t5.py "$OUT/g" "$n" col "artifact/inputs/graphs/$n.col" \
         && cp "$OUT/g/$n.cnf" "$raw" ;;
  esac
  [ -s "$raw" ] || return 1
  grep -v '^c' "$raw" > "$OUT/$n.cnf"; rm -f "$raw"
}
count_of() {  # the count line of a counter's output
  grep -E '^c s exact (arb |quadruple |double )?int ' "$1" | tail -n 1 | awk '{print $NF}'
}
printf 'name\tcounter\texit\tseconds\tcount\tverdict\n' > "$OUT/result.tsv"
fail=0
while IFS=$'\t' read -r name expect _; do
  [ "$name" = name ] && continue
  gen "$name" || { echo "xcheck: cannot generate $name"; fail=1; continue; }
  for c in ganak sstd; do
    t0=$(date +%s.%N)
    if [ $c = ganak ]; then
      timeout "$TO" "$GANAK" --prob 0 "$OUT/$name.cnf" > "$OUT/$name.ganak.out" 2>&1; rc=$?
    else
      tmp=$(mktemp -d "$OUT/sstd.XXXXXX")
      (cd "$SHARPSAT_DIR" && timeout "$TO" ./sharpSAT -decot 1 -decow 100 -tmpdir "$tmp" -cs "$CS" \
         "$OUT/$name.cnf") > "$OUT/$name.sstd.out" 2>&1; rc=$?
      rm -rf "$tmp"
    fi
    s=$(awk -v a="$t0" -v b="$(date +%s.%N)" 'BEGIN{printf "%.1f", b-a}')
    got=$(count_of "$OUT/$name.$c.out")
    v=FAIL; [ -n "$got" ] && [ "$got" = "$expect" ] && v=PASS
    [ $v = PASS ] || fail=1
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$name" "$c" "$rc" "$s" "${got:--}" "$v" >> "$OUT/result.tsv"
    printf '%-10s %-6s exit %-3s %8s s  %s\n' "$name" "$c" "$rc" "$s" "$v"
  done
done < "$X/expected.tsv"
rm -rf "$OUT/g"
echo "xcheck: $(grep -c 'PASS$' "$OUT/result.tsv") PASS, $(grep -c 'FAIL$' "$OUT/result.tsv") FAIL; $OUT/result.tsv"
exit $fail

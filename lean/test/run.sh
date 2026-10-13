#!/usr/bin/env bash
# Regression runner for lean/test: runs every test/*.lean file (or the files named as arguments)
# one at a time from lean/, with the precompiled checker loaded as plugins, and compares the
# normalised output with test/expected/NAME.out.
#
#   test/run.sh                 all tests
#   test/run.sh Jean CountHint  some tests (names with or without test/ and .lean)
#   test/run.sh --update [...]  (re)write the expected outputs from the current tree
#
# Sequential by design: each run loads Mathlib and needs about 3 GB. Build first (`lake build`).
# Normalised: millisecond figures (`123 ms` -> `N ms`), the absolute path of lean/, and the
# per-run scratch directory. Tests that write files get the scratch directory instead of the
# repository (QueensSymExport.lean writes its CNF files to $QSYM_OUT); a test that still
# creates or changes a file anywhere under lean/ (outside .lake) fails.
# Exit status: 0 if every test passes and matches its expected output, 1 otherwise.

set -u

cd "$(dirname "$0")/.." || exit 2
LEAN_DIR=$(pwd)

update=0
names=()
for a in "$@"; do
  case "$a" in
    --update) update=1 ;;
    -h|--help) sed -n '2,15p' "$0"; exit 0 ;;
    *) a=${a#test/}; names+=("${a%.lean}") ;;
  esac
done
if [ ${#names[@]} -eq 0 ]; then
  for f in test/*.lean; do
    b=$(basename "$f"); names+=("${b%.lean}")
  done
fi

case "$(uname -s)" in
  Darwin) ext=dylib ;;
  *) ext=so ;;
esac
plugins=(
  "--plugin=$LEAN_DIR/.lake/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.$ext"
  "--plugin=$LEAN_DIR/.lake/build/lib/libCountCatcher_CountCatcherChecker.$ext"
)
for p in "${plugins[@]}"; do
  if [ ! -f "${p#--plugin=}" ]; then
    echo "run.sh: ${p#--plugin=} not found; run 'lake build' in lean/ first" >&2
    exit 2
  fi
done

tmpbase=${TMPDIR:-/tmp}
scratch=$(mktemp -d "${tmpbase%/}/count-catcher-test.XXXXXX") || exit 2
trap 'rm -rf "$scratch"' EXIT
export QSYM_OUT="$scratch/out"

# Volatile parts of the output: timings, the checkout location, the scratch directory.
normalise() {
  sed -E -e "s#$scratch#<scratch>#g" -e "s#$LEAN_DIR/#<lean>/#g" -e "s#$LEAN_DIR#<lean>#g" \
    -e 's/[0-9]+ ms/N ms/g'
}

mkdir -p test/expected
pass=0; failed=(); total_start=$SECONDS
for name in "${names[@]}"; do
  src="test/$name.lean"
  if [ ! -f "$src" ]; then
    echo "MISSING $name (no $src)"; failed+=("$name"); continue
  fi
  rm -rf "$scratch/out"; mkdir -p "$scratch/out"
  touch "$scratch/marker"
  start=$SECONDS
  lake env lean "${plugins[@]}" "$src" > "$scratch/raw" 2>&1
  status=$?
  secs=$((SECONDS - start))
  normalise < "$scratch/raw" > "$scratch/out.txt"
  # files the test created or changed under lean/ (build outputs in .lake excluded)
  written=$(find . -path ./.lake -prune -o -type f -newer "$scratch/marker" -print 2>/dev/null)
  exp="test/expected/$name.out"
  if [ "$update" -eq 1 ]; then
    cp "$scratch/out.txt" "$exp"
  fi
  if [ "$status" -ne 0 ]; then
    echo "FAIL    $name  ${secs}s  (lean exit $status)"; sed -n '1,20p' "$scratch/out.txt"
    failed+=("$name")
  elif [ -n "$written" ]; then
    echo "FAIL    $name  ${secs}s  (wrote into the repository:" $written ")"
    failed+=("$name")
  elif [ ! -f "$exp" ]; then
    echo "NOEXP   $name  ${secs}s  (no $exp; run with --update)"
    failed+=("$name")
  elif ! diff -u "$exp" "$scratch/out.txt" > "$scratch/diff"; then
    echo "DIFF    $name  ${secs}s"; sed -n '1,40p' "$scratch/diff"
    failed+=("$name")
  else
    echo "PASS    $name  ${secs}s"
    pass=$((pass + 1))
  fi
done

echo "run.sh: $pass passed, ${#failed[@]} failed, $((SECONDS - total_start))s"
if [ ${#failed[@]} -gt 0 ]; then
  echo "run.sh: failed: ${failed[*]}"
  exit 1
fi
exit 0

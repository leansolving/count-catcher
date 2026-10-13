#!/usr/bin/env bash
# count-catcher smoke test, a few minutes after artifact/install.sh:
#   1. the external tools are on PATH and cpog2lrat runs
#   2. lean/test/run.sh Queens8: the 8-queens theorem from its stored certificate
#   3. end to end: bin/count-catcher builds and proves the 6-queens count (4) from the Lean
#      encoder (CNF export, D4, cpog-gen-fwd, cpog2lrat, Lean)
# Prints OK and exits 0 if everything passes, exits 1 otherwise.
set -uo pipefail
ROOT=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")/.." && pwd)
source "$ROOT/artifact/env.sh"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/count-catcher-smoke.XXXXXX")
failed=()
start=$SECONDS

result() {  # result NAME STATUS SECONDS
  if [ "$2" -eq 0 ]; then echo "PASS  $1  ($3 s)"; else echo "FAIL  $1  ($3 s)"; failed+=("$1"); fi
}

# 0. prebuilt tree: do its build outputs belong to these Lean sources? (lean_fingerprint as in
#    artifact/pack_prebuilt.sh; older tarballs without the line are not checked)
want=$(sed -n 's/^lean sources sha256: //p' "$ROOT/tools/PREBUILT.txt" 2>/dev/null)
if [ -n "$want" ]; then
  have=$(cd "$ROOT/lean" && find . -path ./.lake -prune -o \( -name '*.lean' -o -name lakefile.toml \
     -o -name lake-manifest.json -o -name lean-toolchain \) -type f -print | LC_ALL=C sort \
     | xargs sha256sum | sha256sum | cut -d' ' -f1)
  [ "$have" = "$want" ]; st=$?
  [ $st -eq 0 ] || echo "  the prebuilt tarball was built from other Lean sources (tools/PREBUILT.txt); use the matching pair"
  result "prebuilt tree matches the Lean sources" $st 0
fi

# 1. tools
t0=$SECONDS; st=0
for t in d4 cpog-gen-fwd cpog-gen cpog-check cadical drat-trim cpog2lrat lake uv count-catcher; do
  command -v "$t" >/dev/null || { echo "  $t not found on PATH"; st=1; }
done
cpog2lrat --help > "$tmp/cpog2lrat.out" 2>&1   # prints its usage and exits 1
grep -q '^usage: cpog2lrat' "$tmp/cpog2lrat.out" || { echo "  cpog2lrat --help:"; cat "$tmp/cpog2lrat.out"; st=1; }
result "tools on PATH, cpog2lrat --help" $st $((SECONDS - t0))

# 2. one Lean regression test
t0=$SECONDS
timeout 600 "$ROOT/lean/test/run.sh" Queens8 > "$tmp/run.out" 2>&1; st=$?
sed 's/^/  /' "$tmp/run.out"
result "lean/test/run.sh Queens8" $st $((SECONDS - t0))

# 3. end to end
t0=$SECONDS
(cd "$tmp" && timeout 600 count-catcher smoke_queens6 --via 'Queens.card_of_check (n := 6)' --run) \
  > "$tmp/e2e.out" 2>&1; st=$?
grep '^count-catcher:' "$tmp/e2e.out" | sed 's/^/  /'
grep -q '^count-catcher: theorem smoke_queens6 proved, count 4$' "$tmp/e2e.out" || st=1
[ $st -eq 0 ] || { echo "  output:"; tail -n 40 "$tmp/e2e.out" | sed 's/^/  /'; }
result "count-catcher end to end (6-queens, count 4)" $st $((SECONDS - t0))

echo "smoke.sh: $((SECONDS - start)) s"
if [ ${#failed[@]} -gt 0 ]; then
  echo "smoke.sh: FAILED: ${failed[*]} (files kept in $tmp)"
  exit 1
fi
rm -rf "$tmp"
echo OK

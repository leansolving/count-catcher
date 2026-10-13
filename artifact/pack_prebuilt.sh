#!/usr/bin/env bash
# count-catcher: pack the prebuilt tree for the offline route, after a clean online install.
#
#   bash artifact/pack_prebuilt.sh [OUT]      (default OUT: count-catcher-prebuilt-x86_64.tar.zst
#                                             in the repository root; ZSTD_LEVEL, default 19)
#
# The tarball unpacks into the repository root of a checkout of the same commit:
#   zstd -dc count-catcher-prebuilt-x86_64.tar.zst | tar -xf - -C count-catcher
# and makes the tree runnable without network and without writing into the home directory
# (source artifact/env.sh: ELAN_HOME becomes .elan/ of the repository, uv runs offline). Contents:
#   lean/.lake/        the Lean packages (Mathlib, lrat-catcher, ...) and all build outputs
#   tools/             tools/bin and the built trees with their sources (D4, cpog, cpog-fwd,
#                      CaDiCaL, drat-trim), the GMP source tarball and the installed static GMP;
#                      not the cargo target directory or GMP's build directory
#   bin/count-catcher  the driver wrapper; bin/uv, a copy of the uv binary
#   .elan/             elan and the Lean toolchain of lean/lean-toolchain (from $ELAN_HOME or ~/.elan)
#   tools/PREBUILT.txt what was packed, where and when
# Needs GNU tar, zstd and sha256sum. Writes OUT and OUT.sha256 and prints size and time.
# BUILD_OS names the system of the install when packing happens elsewhere (default: this one).

set -euo pipefail
ROOT=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")/.." && pwd)
OUT=$(readlink -f "${1:-$ROOT/count-catcher-prebuilt-x86_64.tar.zst}")
LEVEL=${ZSTD_LEVEL:-19}
die() { echo "pack_prebuilt.sh: $*" >&2; exit 1; }

command -v zstd >/dev/null || die "zstd not found"
tar --version | head -n 1 | grep -q 'GNU tar' || die "needs GNU tar"

# What a clean online install leaves behind.
for t in d4 cpog-gen-fwd cpog-gen cpog-check cadical drat-trim cpog2lrat; do
  [ -x "$ROOT/tools/bin/$t" ] || die "tools/bin/$t missing; run artifact/install.sh first"
done
for f in lean/.lake/build/lib/libCountCatcher_CountCatcherChecker.so \
         lean/.lake/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.so \
         lean/.lake/build/lib/lean/CountCatcher.olean; do
  [ -f "$ROOT/$f" ] || die "$f missing; run artifact/install.sh first"
done
E=${ELAN_HOME:-$HOME/.elan}
TC=$(sed 's|/|--|; s|:|---|' "$ROOT/lean/lean-toolchain")   # leanprover/lean4:v4.30.0 -> directory name
[ -d "$E/toolchains/$TC" ] || die "Lean toolchain $E/toolchains/$TC missing"
[ "$(basename "$E")" = .elan ] || die "ELAN_HOME must end in .elan (is $E)"
UV=$(PATH="$ROOT/bin:$HOME/.local/bin:$PATH" command -v uv) || die "uv not found"

# The wrapper of this checkout, and uv next to it.
bash "$ROOT/artifact/install.sh" --step wrapper > /dev/null 2>&1
[ "$(readlink -f "$UV")" = "$ROOT/bin/uv" ] || cp "$UV" "$ROOT/bin/uv"
GMP_TB=$(cd "$ROOT/tools" && ls gmp-*.tar.xz)
# Fingerprint of the Lean sources the build outputs belong to (smoke.sh compares it).
lean_fingerprint() {
  (cd "$ROOT/lean" && find . -path ./.lake -prune -o \( -name '*.lean' -o -name lakefile.toml \
     -o -name lake-manifest.json -o -name lean-toolchain \) -type f -print | LC_ALL=C sort \
     | xargs sha256sum | sha256sum | cut -d' ' -f1)
}

{
  echo "count-catcher prebuilt tree for x86_64 Linux (offline installation route)"
  echo "packed:    $(date -u '+%F %T UTC') on $(hostname) ($(uname -sr))"
  echo "built in:  ${BUILD_OS:-$( (. /etc/os-release 2>/dev/null && echo "$PRETTY_NAME") || echo unknown)} by artifact/install.sh"
  echo "commit:    $(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo "none (not a git checkout)")"
  echo "lean sources sha256: $(lean_fingerprint)"
  echo "lean:      $(cat "$ROOT/lean/lean-toolchain"), mathlib $(grep -A5 'mathlib4.git' "$ROOT/lean/lake-manifest.json" | sed -n 's/.*"rev": "\(.\{12\}\).*/\1/p')"
  for d in d4 cpog cadical drat-trim; do
    echo "$d: $(git -C "$ROOT/tools/$d" rev-parse --short=12 HEAD 2>/dev/null)"
  done
  echo "gmp:       $GMP_TB (static, fat)"
  echo "uv:        $("$ROOT/bin/uv" --version)"
} > "$ROOT/tools/PREBUILT.txt"

EL=(.elan/bin ".elan/toolchains/$TC")
[ -f "$E/settings.toml" ] && EL+=(.elan/settings.toml)
echo "packing into $OUT (zstd -$LEVEL)"
t0=$SECONDS
tar -cf - --owner=0 --group=0 --numeric-owner \
    --exclude=tools/cpog2lrat-target --exclude="tools/${GMP_TB%.tar.xz}" \
    -C "$ROOT" lean/.lake tools bin/count-catcher bin/uv \
    -C "$(dirname "$E")" "${EL[@]}" \
  | zstd -q -T0 -"$LEVEL" -o "$OUT.part"
mv "$OUT.part" "$OUT"
secs=$((SECONDS - t0))
(cd "$(dirname "$OUT")" && sha256sum "$(basename "$OUT")" > "$OUT.sha256")
echo "size $(stat -c %s "$OUT") bytes ($(du -h "$OUT" | cut -f1)), $secs s, sha256 $(cut -d' ' -f1 "$OUT.sha256")"

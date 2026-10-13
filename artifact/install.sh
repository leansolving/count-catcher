#!/usr/bin/env bash
# count-catcher: build everything from source (the online installation route).
#
#   bash artifact/install.sh [--no-apt] [--apt-only] [--jobs N]
#
#   --no-apt    skip the apt step (the packages of artifact/apt-packages.txt must be present)
#   --apt-only  run only the apt step
#   --jobs N    parallel build jobs (default: nproc)
#
# Needs x86_64 Linux (tested on Ubuntu 25.04, the TACAS 2026 AE VM), about 13 GB of disk and
# network access (GitHub, gnu.org, Mathlib's cache server, rust-lang.org, astral.sh; about
# 1.5 GB of downloads). Run it from the
# repository root or from anywhere: it works on the repository it belongs to. Idempotent: a
# second run skips or quickly redoes what is already built. Everything goes into the repository
# (tools/, lean/.lake, bin/) and into the home directory (~/.elan, ~/.cargo, ~/.rustup,
# ~/.local/bin, ~/.cache); the shell start-up files are not touched (source artifact/env.sh).
#
# Steps (output in artifact/logs/STEP.log; time and peak memory in artifact/logs/steps.tsv):
#   apt        sudo apt-get install of the packages of artifact/apt-packages.txt not yet installed
#   tools      D4 (linked with a static GMP built from source), cpog-gen and cpog-check,
#              cpog-gen-fwd (cpog with tools-src/*.patch), CaDiCaL and drat-trim, at pinned
#              commits, into tools/ (binaries in tools/bin)
#   cpog2lrat  rustup (only if cargo is missing) and cargo build of tools-src/cpog2lrat
#   uv         the Python launcher uv 0.12.23 into ~/.local/bin (only if no uv is on PATH)
#   elan       elan into ~/.elan and the Lean toolchain of lean/lean-toolchain
#   mathlib    the Lean dependencies (Mathlib, lrat-catcher) and Mathlib's prebuilt cache
#   lean       lake build: CountCatcherChecker, CountCatcherMath, CountCatcher
#   wrapper    bin/count-catcher, the driver scripts/count_catcher.py run through uv
# Afterwards: source artifact/env.sh && artifact/smoke.sh

set -euo pipefail

SELF=$(readlink -f "${BASH_SOURCE[0]}")
ROOT=$(cd "$(dirname "$SELF")/.." && pwd)
T=$ROOT/tools
LOGS=$ROOT/artifact/logs
STATS=$LOGS/steps.tsv

# Pinned versions (the commits of the paper's runs).
D4_REPO=crillab/d4;            D4_REV=333370cc1e843dd0749c1efe88516e72b5239174
CPOG_REPO=rebryant/cpog;       CPOG_REV=a97ed8543d8368a234f715cf8b1a7aa38bc96c3d
CADICAL_REPO=arminbiere/cadical; CADICAL_REV=c60730422e758ef1cebe7aeddf2dda31c996bf04  # 3.0.1
DRAT_REPO=marijnheule/drat-trim; DRAT_REV=2e3b2dc0ecf938addbd779d42877b6ed69d9a985
GMP_VER=6.3.0
GMP_SHA256=a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898
GMP_URLS="https://ftp.gnu.org/gnu/gmp https://ftpmirror.gnu.org/gmp https://gmplib.org/download/gmp"
ELAN_INIT=https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
UV_VER=0.12.23   # the uv of the prebuilt tarball

export PATH="$T/bin:$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"

NO_APT=0; APT_ONLY=0; STEP=""
JOBS=$(nproc 2>/dev/null || echo 4)
while [ $# -gt 0 ]; do
  case "$1" in
    --no-apt) NO_APT=1 ;;
    --apt-only) APT_ONLY=1 ;;
    --jobs) JOBS=${2:?--jobs needs a number}; shift ;;
    --jobs=*) JOBS=${1#--jobs=} ;;
    --step) STEP=${2:?}; shift ;;   # internal: run one step (called through measure.py)
    -h|--help) awk 'NR > 1 && /^#/ {sub(/^# ?/, ""); print; next} NR > 1 {exit}' "$SELF"; exit 0 ;;
    *) echo "install.sh: unknown option $1 (try --help)" >&2; exit 2 ;;
  esac
  shift
done
case "$JOBS" in ''|*[!0-9]*|0) echo "install.sh: --jobs needs a positive number" >&2; exit 2 ;; esac
export JOBS

say() { printf '[install %s] %s\n' "$(date +%H:%M:%S)" "$*"; }
die() { printf '[install] ERROR: %s\n' "$*" >&2; exit 1; }

# ---------------------------------------------------------------------------------------------
# Steps. Each runs in its own shell (bash install.sh --step NAME) under measure.py, with its
# output in artifact/logs/NAME.log.

clone() {  # clone REPO DIR REV: clone once, then check out the pinned commit
  local repo=$1 dir=$2 rev=$3
  [ -d "$dir/.git" ] || git clone -q "https://github.com/$repo.git" "$dir"
  if ! git -C "$dir" checkout -q "$rev" 2>/dev/null; then
    git -C "$dir" fetch -q origin
    git -C "$dir" checkout -q "$rev"
  fi
}

step_tools() {
  mkdir -p "$T/bin"
  cd "$T"
  clone "$D4_REPO" d4 "$D4_REV"
  clone "$CPOG_REPO" cpog "$CPOG_REV"
  clone "$CADICAL_REPO" cadical "$CADICAL_REV"
  clone "$DRAT_REPO" drat-trim "$DRAT_REV"

  # GMP, static, with C++ support and runtime CPU dispatch (--enable-fat): the binaries do not
  # depend on the CPU of the build machine (D4 needs GMP's C++ interface, gmpxx).
  if [ ! -f "$T/gmp/lib/libgmpxx.a" ]; then
    local tb=gmp-$GMP_VER.tar.xz ok=0
    if [ ! -f "$tb" ] || ! echo "$GMP_SHA256  $tb" | sha256sum -c --quiet - 2>/dev/null; then
      for u in $GMP_URLS; do
        if curl -fsSL --retry 3 -o "$tb.part" "$u/$tb" \
           && echo "$GMP_SHA256  $tb.part" | sha256sum -c --quiet -; then
          mv "$tb.part" "$tb"; ok=1; break
        fi
      done
      [ "$ok" = 1 ] || { echo "could not download $tb with the expected checksum"; exit 1; }
    fi
    rm -rf "gmp-$GMP_VER" gmp
    tar xf "$tb"
    # -std=gnu17: GCC 15 (Ubuntu 26.04) defaults to C23, which GMP 6.3.0's configure tests fail
    # ("could not find a working compiler"); gnu17 is GCC 14's default, so 25.04 builds the same.
    (cd "gmp-$GMP_VER" && ./configure CC="gcc -std=gnu17" --enable-cxx --enable-fat --disable-shared \
       --with-pic --prefix="$T/gmp" && make -j"$JOBS" && make install)
  fi

  # D4. One-line fix: DAG.hh declares a virtual method without a body (GCC links it only by
  # luck, clang not at all); C++14 for current Boost headers; -no-pie for the non-PIC PaToH
  # library that D4 ships.
  sed -i 's|^  virtual T computeNbModels();|  virtual T computeNbModels() { assert(0); return T(); }|' d4/DAG/DAG.hh
  make -C d4 -j"$JOBS" CXX="g++ -std=c++14 -I$T/gmp/include" LDFLAGS="-L$T/gmp/lib -no-pie"

  # cpog-gen and cpog-check, unpatched except for two leftover debug printf lines in
  # cpog-check (one per clause lookup; a 50x slowdown), now printed only at verbosity 4.
  sed -i -e 's|^    printf("Looking for clause %d.  Got block|    if (verb_level >= 4) printf("Looking for clause %d.  Got block|' \
         -e 's|^\tprintf("Looking for clause %d.  lid = |\tif (verb_level >= 4) printf("Looking for clause %d.  lid = |' \
         cpog/src/cpog-check.c
  make -C cpog/src -j"$JOBS" CC="gcc -std=gnu17" install   # gnu17: see GMP above

  # cpog-gen-fwd: cpog-gen with tools-src/cpog-gen-noreverse.patch and cpog-gen-fwd.patch.
  # Rebuilt from a fresh copy whenever the patches change (stamp: their checksums).
  local stamp
  stamp=$(cat "$ROOT/tools-src/cpog-gen-noreverse.patch" "$ROOT/tools-src/cpog-gen-fwd.patch" | sha256sum | cut -d' ' -f1)
  if [ ! -x cpog-fwd/src/cpog-gen ] || [ "$(cat cpog-fwd/.patches 2>/dev/null)" != "$stamp" ]; then
    rm -rf cpog-fwd
    mkdir cpog-fwd
    git -C cpog archive "$CPOG_REV" src | tar -x -C cpog-fwd
    # patch, not git apply: inside a git work tree git apply resolves paths from its top level
    (cd cpog-fwd && patch -p1 -s < "$ROOT/tools-src/cpog-gen-noreverse.patch" \
                 && patch -p1 -s < "$ROOT/tools-src/cpog-gen-fwd.patch")
    make -C cpog-fwd/src -j"$JOBS" CC="gcc -std=gnu17" cpog-gen
    echo "$stamp" > cpog-fwd/.patches
  fi
  cp cpog-fwd/src/cpog-gen bin/cpog-gen-fwd

  # CaDiCaL (cpog-gen calls it), drat-trim (gnu99: GCC 14 rejects the implicit getc_unlocked
  # under -std=c99).
  [ -f cadical/build/makefile ] || (cd cadical && ./configure)
  make -C cadical/build -j"$JOBS"
  gcc drat-trim/drat-trim.c -std=gnu99 -O2 -o drat-trim/drat-trim

  ln -sf ../d4/d4 bin/d4
  ln -sf ../cadical/build/cadical bin/cadical
  ln -sf ../drat-trim/drat-trim bin/drat-trim
  ln -sf ../cpog/src/cpog-gen bin/cpog-gen
  ln -sf ../cpog/src/cpog-check bin/cpog-check

  # Functional check: D4 counts the 3 models of (x1 or x2).
  printf 'p cnf 2 1\n1 2 0\n' > "$T/selftest.cnf"
  local out; out=$(bin/d4 "$T/selftest.cnf" -mc)
  rm -f "$T/selftest.cnf"
  grep -q '^s 3$' <<< "$out" || { echo "D4 self-test failed"; exit 1; }
  bin/cadical --version
  ls -l bin/
}

step_cpog2lrat() {
  if ! command -v cargo >/dev/null; then
    local tmp; tmp=$(mktemp -d)
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs -o "$tmp/rustup-init.sh"
    sh "$tmp/rustup-init.sh" -y --profile minimal --no-modify-path
    rm -rf "$tmp"
  fi
  cargo --version
  CARGO_TARGET_DIR=$T/cpog2lrat-target cargo build --release -j "$JOBS" \
    --manifest-path "$ROOT/tools-src/cpog2lrat/Cargo.toml"
  mkdir -p "$T/bin"
  cp "$T/cpog2lrat-target/release/cpog2lrat" "$T/bin/cpog2lrat"
}

step_uv() {
  if ! command -v uv >/dev/null; then
    if ! curl -LsSf "https://astral.sh/uv/$UV_VER/install.sh" | env UV_NO_MODIFY_PATH=1 INSTALLER_NO_MODIFY_PATH=1 sh; then
      # fallback: pip (Ubuntu marks its Python as externally managed, hence the flag)
      pip3 install --user --break-system-packages "uv==$UV_VER"
    fi
  fi
  uv --version
}

step_elan() {
  local tc; tc=$(cat "$ROOT/lean/lean-toolchain")
  if ! command -v elan >/dev/null; then
    local tmp; tmp=$(mktemp -d)
    curl -sSfL "$ELAN_INIT" -o "$tmp/elan-init.sh"
    sh "$tmp/elan-init.sh" -y --default-toolchain none --no-modify-path
    rm -rf "$tmp"
  fi
  elan --version
  elan toolchain list | grep -qF "$tc" || elan toolchain install "$tc"
  (cd "$ROOT/lean" && lean --version && lake --version)
}

step_mathlib() {
  cd "$ROOT/lean"
  # LEAN_NUM_THREADS: Lean and Lake otherwise size their thread pools by the machine's CPUs
  # and ignore the affinity mask (and --jobs).
  LEAN_NUM_THREADS=$JOBS lake exe cache get
}

step_lean() {
  cd "$ROOT/lean"
  LEAN_NUM_THREADS=$JOBS lake build
  local ext=so
  for f in .lake/build/lib/libCountCatcher_CountCatcherChecker.$ext \
           .lake/packages/LRATCatcher/.lake/build/lib/libLRATCatcher_LRATCatcher.$ext \
           .lake/build/lib/lean/CountCatcher.olean; do
    [ -f "$f" ] || { echo "missing build output $f"; exit 1; }
  done
}

step_wrapper() {
  mkdir -p "$ROOT/bin"
  cat > "$ROOT/bin/count-catcher" <<'EOF'
#!/usr/bin/env bash
# count-catcher: runs the driver scripts/count_catcher.py through uv (written by
# artifact/install.sh). Relative paths in the arguments are taken from the current directory;
# the output goes to ./count-catcher-out/NAME unless --dir is given.
#   count-catcher queens6 --via 'Queens.card_of_check (n := 6)' --run
#   count-catcher NAME --dimacs FILE.cnf --run
#   count-catcher --help
ROOT=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")/.." && pwd)
source "$ROOT/artifact/env.sh"
exec uv run --no-project "$ROOT/scripts/count_catcher.py" "$@"
EOF
  chmod +x "$ROOT/bin/count-catcher"
}

if [ -n "$STEP" ]; then
  PS4='+ '
  set -x
  "step_$STEP"
  exit 0
fi

# ---------------------------------------------------------------------------------------------
# Driver.

run_step() {  # run_step NAME: one step under measure.py; on failure show the log's tail
  local name=$1 log=$LOGS/$1.log rc=0
  : > "$log"
  say "$name ... (log: ${log#$ROOT/})"
  if [ -n "$PYTHON" ]; then
    "$PYTHON" "$ROOT/artifact/measure.py" "$name" "$log" "$STATS" -- \
      bash "$SELF" --step "$name" --jobs "$JOBS" || rc=$?
  else
    local t0=$SECONDS
    bash "$SELF" --step "$name" --jobs "$JOBS" >> "$log" 2>&1 || rc=$?
    printf '%s\t%s\t%s\t-\t-\t-\n' "$name" "$rc" "$((SECONDS - t0))" >> "$STATS"
  fi
  if [ "$rc" -ne 0 ]; then
    echo "----- last lines of ${log#$ROOT/} -----" >&2
    tail -n 30 "$log" >&2
    die "step $name failed (exit $rc); full output in $log"
  fi
  say "$name done ($(tail -n 1 "$STATS" | cut -f3) s)"
}

apt_missing() {
  local p
  for p in $(sed 's/#.*//' "$ROOT/artifact/apt-packages.txt"); do
    dpkg-query -W -f='${Status}\n' "$p" 2>/dev/null | grep -q '^install ok installed' || echo "$p"
  done
}

do_apt() {
  if ! command -v dpkg-query >/dev/null; then
    say "apt: not a Debian/Ubuntu system; install the equivalents of artifact/apt-packages.txt yourself"
    return 0
  fi
  local missing; missing=$(apt_missing | xargs)
  if [ -z "$missing" ]; then
    say "apt: all packages of artifact/apt-packages.txt are installed"
    return 0
  fi
  if [ "$NO_APT" = 1 ]; then
    say "apt: skipped (--no-apt), not installed: $missing; the tools step may fail"
    return 0
  fi
  say "apt: installing $missing (sudo)"
  local t0=$SECONDS sudo=sudo
  [ "$(id -u)" = 0 ] && sudo=""
  if ! { $sudo apt-get update && $sudo env DEBIAN_FRONTEND=noninteractive apt-get install -y $missing; }; then
    cat >&2 <<EOF
[install] apt-get failed. Ubuntu 25.04 reached its end of life in January 2026; once its
packages move to old-releases.ubuntu.com, archive.ubuntu.com answers 404. Point apt there and
rerun this script:
  sudo sed -i -e 's|http://[a-z.]*archive.ubuntu.com|http://old-releases.ubuntu.com|' \\
              -e 's|http://security.ubuntu.com|http://old-releases.ubuntu.com|' \\
              /etc/apt/sources.list.d/ubuntu.sources
EOF
    die "apt step failed"
  fi
  printf 'apt\t0\t%s\t-\t-\t-\n' "$((SECONDS - t0))" >> "$STATS"
  missing=$(apt_missing | xargs)
  [ -z "$missing" ] || die "apt: still not installed: $missing"
}

summary() {
  echo
  echo "================ count-catcher installation summary ================"
  echo "machine: $(nproc) CPUs (--jobs $JOBS), $(awk '/MemTotal/ {printf "%.1f GiB", $2/1048576}' /proc/meminfo) RAM"
  echo
  printf '%-10s %6s %9s %14s %14s %16s\n' step exit "wall s" "peak PSS MiB" "peak RSS MiB" "cgroup anon MiB"
  awk -F'\t' '{printf "%-10s %6s %9s %14s %14s %16s\n", $1, $2, $3, $4, $5, $6; s += $3}
              END {printf "%-10s %6s %9s\n", "total", "", s}' "$STATS"
  echo "(PSS: memory of the step's processes, shared pages counted once; RSS: summed per process)"
  echo
  echo "versions:"
  v() { printf '  %-12s %s\n' "$1" "$2"; }
  v lean "$(cd "$ROOT/lean" && lean --version 2>/dev/null | head -n 1)"
  v lake "$(cd "$ROOT/lean" && lake --version 2>/dev/null | head -n 1)"
  v elan "$(elan --version 2>/dev/null | head -n 1)"
  v mathlib "$(grep -A5 '"url": "https://github.com/leanprover-community/mathlib4.git"' "$ROOT/lean/lake-manifest.json" | sed -n 's/.*"rev": "\(.\{12\}\).*/\1/p')"
  v lrat-catcher "$(git -C "$ROOT/lean/.lake/packages/LRATCatcher" rev-parse --short=12 HEAD 2>/dev/null)"
  v d4 "$(git -C "$T/d4" rev-parse --short=12 HEAD 2>/dev/null) (GMP $GMP_VER static, fat)"
  v cpog "$(git -C "$T/cpog" rev-parse --short=12 HEAD 2>/dev/null) (cpog-gen, cpog-check; cpog-gen-fwd with tools-src/*.patch)"
  v cadical "$(cadical --version 2>/dev/null)"
  v drat-trim "$(git -C "$T/drat-trim" rev-parse --short=12 HEAD 2>/dev/null)"
  v cpog2lrat "$(cargo --version 2>/dev/null)"
  v uv "$(uv --version 2>/dev/null)"
  v gcc "$(gcc --version 2>/dev/null | head -n 1)"
  echo
  echo "disk:"
  for d in "$ROOT/lean/.lake" "$T" "$HOME/.elan" "$HOME/.cache/mathlib" "$HOME/.cargo" "$HOME/.rustup" "$HOME/.local/share/uv" "$HOME/.cache/uv"; do
    [ -e "$d" ] && printf '  %8s  %s\n' "$(du -sh "$d" 2>/dev/null | cut -f1)" "$d"
  done
  echo
  echo "next: source $ROOT/artifact/env.sh && $ROOT/artifact/smoke.sh"
}

[ "$(uname -s)" = Linux ] && [ "$(uname -m)" = x86_64 ] \
  || die "needs x86_64 Linux (D4 links a prebuilt x86_64 Linux PaToH library); found $(uname -s) $(uname -m)"
mkdir -p "$LOGS"
: > "$STATS"
say "repository $ROOT, $(nproc) CPUs, --jobs $JOBS, $(df -hP "$ROOT" | awk 'NR==2 {print $4}') free"
# About 9 GB go into the repository (lean/.lake) and 4 GB into the home directory.
for d in "$ROOT" "$HOME"; do
  free_gb=$(df -Pk "$d" | awk 'NR==2 {print int($4 / 1048576)}')
  [ "$free_gb" -ge 15 ] || say "warning: only $free_gb GB free under $d; the installation needs about 13 GB"
done

do_apt
[ "$APT_ONLY" = 1 ] && exit 0

missing=""
for c in git curl make gcc g++ tar xz patch sha256sum; do
  command -v "$c" >/dev/null || missing="$missing $c"
done
[ -z "$missing" ] || die "commands not found:$missing (on Ubuntu: sudo apt-get install build-essential git curl xz-utils)"
PYTHON=$(command -v python3 || true)
[ -n "$PYTHON" ] || say "python3 not found: no memory figures (uv still works)"

run_step tools
run_step cpog2lrat
run_step uv
run_step elan
say "mathlib: downloads the Lean dependencies and Mathlib's prebuilt files (several GB)"
run_step mathlib
say "lean: compiles count-catcher's Lean libraries"
run_step lean
run_step wrapper
summary | tee "$LOGS/summary.txt"

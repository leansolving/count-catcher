#!/bin/bash
# Build the native cpog2lrat and install it into BIN (default: tools/bin of this repository).
# Mac:     tools-src/cpog2lrat/build.sh
# Cluster: tools-src/cpog2lrat/build.sh /home1/szeider/mccert/tools/bin
# Site defaults of our Slurm cluster; adjust the paths before use elsewhere.
# Portable x86-64 code (no -march=native): the login node is Ice Lake, the compute nodes are
# Zen 4, Zen 2 and Broadwell.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd)
BIN=${1:-$D/../../tools/bin}
export PATH=$HOME/.cargo/bin:/home1/szeider/.cargo/bin:$PATH
# macOS: link with the Command Line Tools if the Xcode license has not been accepted.
if [ "$(uname)" = Darwin ] && [ -d /Library/Developer/CommandLineTools ]; then
  export DEVELOPER_DIR=${DEVELOPER_DIR:-/Library/Developer/CommandLineTools}
fi
cargo build --release -q --manifest-path "$D/Cargo.toml"
mkdir -p "$BIN"
cp "$D/target/release/cpog2lrat" "$BIN/cpog2lrat"
echo "installed $BIN/cpog2lrat"

# count-catcher environment. Source it in each new shell:   source artifact/env.sh
# Puts bin/ (count-catcher, and uv in the prebuilt tree), the external tools (tools/bin), Lean
# (elan), cargo and uv on PATH. Online install (artifact/install.sh): elan in ~/.elan, cargo in
# ~/.cargo, uv in ~/.local/bin. Prebuilt tarball (offline): the Lean toolchain is in .elan/ of
# the repository, so ELAN_HOME points there; uv runs offline and without a cache, so nothing is
# written into the home directory.
_cc_root=$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/.." && pwd)
export COUNT_CATCHER_ROOT=$_cc_root
export PATH="$_cc_root/bin:$_cc_root/tools/bin:$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
if [ -d "$_cc_root/.elan/toolchains" ]; then
  export ELAN_HOME=$_cc_root/.elan
  export PATH="$_cc_root/bin:$ELAN_HOME/bin:$PATH"
  export UV_OFFLINE=1 UV_NO_CACHE=1
fi
export UV_PYTHON_DOWNLOADS=never   # the Python scripts run on the system's python3
unset _cc_root

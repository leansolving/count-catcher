#!/usr/bin/env bash
# count-catcher: reproduce the paper's results that run on one machine (4 cores, 14 GB).
#
#   artifact/reproduce.sh --list                      the stages, their wall time and memory
#   artifact/reproduce.sh --all [--skip-large]        every stage, then the PASS/FAIL table
#   artifact/reproduce.sh --stage NAME [NAME ...]     some stages
#   options: --jobs N (parallelism inside an item, default min(4, CPUs)), --keep-files
#
# Results: artifact/out/results.tsv (one line per item), logs in artifact/out/STAGE/; the table
# of artifact/check.py against artifact/expected.tsv at the end (exit 1 on any FAIL). Needs the
# installation of artifact/install.sh; the details are in artifact/reproduce.py.
ROOT=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")/.." && pwd)
# shellcheck source=/dev/null
source "$ROOT/artifact/env.sh"
exec python3 "$ROOT/artifact/reproduce.py" "$@"

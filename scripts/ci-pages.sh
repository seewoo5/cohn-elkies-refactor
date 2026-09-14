#!/usr/bin/env bash

set -euo pipefail

# Cap the number of concurrent Lean processes (each chapter loads the whole `CohnElkies` library).
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"

lake exe vbp build

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json

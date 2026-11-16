#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS=1
echo "Checked head: $(git rev-parse HEAD)"
lake build Girth.Track1GeneralSelectedFamily
log="${1:-/tmp/track1-general-selected-axioms.log}"
lake env lean CheckTrack1GeneralSelectedFamily.lean > "$log" 2>&1
cat "$log"
python3 scripts/check_axioms.py "$log" CheckTrack1GeneralSelectedFamily.lean

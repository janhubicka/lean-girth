#!/usr/bin/env bash
# Focused Track 1 Lean check. Requires the pinned lake/elan toolchain locally.
# Not part of the default Girth.lean build; run on candidate branch explicitly.
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: lake not installed; no Lean validation has taken place." >&2
  exit 127
fi
log="${1:-/tmp/track1-lean-exact-head.log}"
echo "Git head: $(git rev-parse HEAD)"
echo "Toolchain: $(cat lean-toolchain)"
echo "Running: lake env lean CheckTrack1.lean"
set +e
lake env lean CheckTrack1.lean > "$log" 2>&1
code=$?
set -e
cat "$log"
if (( code != 0 )); then
  echo "ERROR: Lean elaboration failed (exit $code)" >&2
  exit "$code"
fi
if grep -E '(sorryAx|_sorry|unknown constant|unknown identifier)' "$log"; then
  echo "ERROR: focused Track 1 proof output needs review" >&2
  exit 1
fi
echo "Focused source elaboration passed, no sorryAx in printed axioms."
echo "This is NOT a certificate for the final selected partite/fusion theorem."
echo "Review all printed axioms, including the external EHN dependency."

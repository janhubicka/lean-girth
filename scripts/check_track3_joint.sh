#!/usr/bin/env bash
# Exact-source local Track 3 gate. Run from the lean-girth repository root.
# This script does not download dependencies, change pins, or trigger Actions.
set -euo pipefail

if [[ ! -f lean-toolchain || ! -f lakefile.toml ]]; then
  echo 'Run from the root of the pinned lean-girth checkout.' >&2
  exit 2
fi
command -v lake >/dev/null || {
  echo 'Missing lake: restore the repository-pinned Lean toolchain first.' >&2
  exit 2
}
command -v python3 >/dev/null || {
  echo 'Missing python3: required by the strict axiom parser.' >&2
  exit 2
}

# The project has substantial Mathlib dependencies. Single-threaded Lean
# avoids runaway cache pressure in 4 GiB agent containers.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
echo "Toolchain pin: $(cat lean-toolchain)"
echo "Repository HEAD: $(git rev-parse HEAD 2>/dev/null || echo unavailable)"
echo 'Building exact Track 3 joint theorem and dependencies ...'
lake build Girth.TrainTrack3JointGeometryParameters Girth.TrainTrack3StageJointGeometryParameters

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
echo 'Elaborating #check and #print axioms for all five Track 3 declarations ...'
lake env lean CheckTrack3JointGeometryParameters.lean | tee "$tmp"
python3 scripts/check_axioms.py "$tmp" CheckTrack3JointGeometryParameters.lean

echo 'Track 3 source-only joint geometry/parameters: strict local gate PASS'

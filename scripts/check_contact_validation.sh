#!/usr/bin/env bash
# Build the complete current proof and audit its transitive logical assumptions.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build +Girth
audit_dir=$(mktemp -d)
trap 'rm -rf "$audit_dir"' EXIT
for audit in CheckContactCore.lean CheckContactValidation.lean CheckContactManuscript.lean; do
  log="$audit_dir/${audit%.lean}.log"
  lake env lean "$audit" | tee "$log"
  python3 scripts/check_axioms.py "$log" "$audit"
done

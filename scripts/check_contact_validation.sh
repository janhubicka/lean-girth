#!/usr/bin/env bash
# Build the complete current proof and audit its transitive logical assumptions.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/test_check_axioms.py
# The additional roots supply older immutable manuscript references. They
# are audited alongside the active proof without changing the default target.
lake build +Girth \
  +Girth.ContactBoostDistinctImages \
  +Girth.TrainWagonStrongInduced \
  +Girth.TrainFillingTemplateConstruction \
  +Girth.TrainFillingInheritedTrain \
  +Girth.TrainFillingInheritedParameters
audit_dir=$(mktemp -d)
trap 'rm -rf "$audit_dir"' EXIT
for audit in CheckContactCore.lean CheckContactValidation.lean CheckContactManuscript.lean; do
  log="$audit_dir/${audit%.lean}.log"
  lake env lean "$audit" | tee "$log"
  python3 scripts/check_axioms.py "$log" "$audit"
done

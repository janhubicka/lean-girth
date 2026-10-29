#!/usr/bin/env bash
set -euo pipefail

# Lane-local gate. Shared umbrella imports and lean.yml belong to integration.
lake build \
  Girth.ForestCyclicSwitching \
  Girth.ForestBottomSupremePullback \
  Girth.ForestToSupremeCycle \
  Girth.ForestActualRecursiveIncrement \
  Girth.ForestToSupremeActualGeometry \
  Girth.TrainRecursiveWitnessPass

checks=(
  CheckForestCyclicSwitching
  CheckForestBottomSupremePullback
  CheckForestToSupremeBottom
  CheckForestToSupremeLeaf
  CheckForestToSupremeCycle
  CheckForestActualRecursiveSupport
  CheckForestActualRecursiveIncrement
  CheckForestToSupremeActualGeometry
  CheckTrainRecursiveWitness
  CheckTrainRecursiveWitnessPass
)

for check in "${checks[@]}"; do
  lake env lean "${check}.lean" | tee "${check}.log"
  python3 scripts/check_axioms.py "${check}.log" "${check}.lean"
done

python3 scripts/check_boundary_transport.py
python3 scripts/check_boundary_girth.py
python3 scripts/check_order_one_bridge.py
python3 scripts/check_output_connector_layout.py

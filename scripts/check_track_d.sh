#!/usr/bin/env bash
set -euo pipefail

# Lane-local gate. Shared umbrella imports and lean.yml belong to integration.
# Building every module also checks files outside the shared import facade.
python3 - <<'PY'
from pathlib import Path
import subprocess

modules = sorted(str(p.with_suffix('')).replace('/', '.')
                 for p in Path('Girth').rglob('*.lean'))
subprocess.run(['lake', 'build', 'Girth', *modules], check=True)
PY

checks=(
  CheckTrackDRootedForest
  CheckForestCyclicSwitching
  CheckForestBottomSupremePullback
  CheckForestOrderSegmentBudget
  CheckForestToSupremeBottom
  CheckForestToSupremeLeaf
  CheckForestToSupremeCycle
  CheckForestActualRecursiveSupport
  CheckForestActualRecursiveIncrement
  CheckForestRecursiveOutputGirth
  CheckTrainRecursiveBaseRamsey
  CheckForestSelectedMixedCoverage
  CheckForestRecursiveInitialMixed
  CheckForestToSupremeActualGeometry
  CheckTrainRecursiveWitness
  CheckTrainRecursiveWitnessPass
  CheckTrainRecursiveWitnessInitial
  CheckTrainRecursiveWitnessInitialParameters
  CheckTrainRecursiveWitnessInitialSupreme
  CheckTrainRecursiveWitnessInitialStage
  CheckTrainRecursiveWitnessProfiles
  CheckTrainRecursiveWitnessConstruction
  CheckTrainRecursiveRefinement
  CheckTrainRecursiveRefinementInitial
  CheckTrainRecursiveRefinementReady
  CheckTrainEdgeOnlyConstantParent
  CheckTrainRecursiveInitialTailLocalization
  CheckTrainRecursiveInitialTailGirth
  CheckTrainRecursiveInitialTailBudget
  CheckTrainRecursiveInitialTailIncidence
  CheckTrainRecursiveInitialTailSystem
  CheckTrainRecursiveInitialTargetStage
  CheckTrainRecursiveReadyConstruction
  CheckTrainRecursiveOneEdgeTarget
  CheckTrainRecursiveRefinementStepGirth
  CheckTrainRecursiveRefinementGirthGain
  CheckTrainRecursiveRefinementForget
)

for check in "${checks[@]}"; do
  lake env lean "${check}.lean" | tee "${check}.log"
  python3 scripts/check_axioms.py "${check}.log" "${check}.lean"
done

python3 scripts/check_boundary_transport.py
python3 scripts/check_boundary_girth.py
python3 scripts/check_order_one_bridge.py
python3 scripts/check_output_connector_layout.py

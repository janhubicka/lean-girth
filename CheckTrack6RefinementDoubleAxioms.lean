import Girth.TrainRecursivePhysicalFineGirthDouble
import Girth.TrainRecursiveRefinementSelectedTransport
import Girth.TrainRecursiveRefinementSinglePartAcyclic

set_option autoImplicit false
set_option Elab.async false

/-!
# Track 6 independent strict axiom inspection entrypoint

EXACT-HEAD KERNEL CHECK IS PENDING. This file imports all six
candidate Track 6 proof modules. The statements below deliberately name
the actual elaborated theorem constants, not source comments or
historical validation markers. A successful run must inspect the
printed axiom sets and reject any sorryAx/unapproved axiom.

Pinned toolchain: leanprover/lean4:v4.35.0-rc3.
Build the imported modules first, in dependency order. Lake imports
precompiled .olean modules, not unbuilt source files:
  LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementDoubleCount
  LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementDoubleStep
  LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementDoubleGirth
  LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursivePhysicalFineGirthDouble
  LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementSelectedTransport
  LEAN_NUM_THREADS=1 lake build +Girth.TrainRecursiveRefinementSinglePartAcyclic
Then execute from the repository root:
  LEAN_NUM_THREADS=1 lake env lean CheckTrack6RefinementDoubleAxioms.lean
This is *not* a substitute for checking the selected lower witness.
-/

#print axioms StructuralRamsey.Girth.card_double_le_of_two_preimages
#print axioms StructuralRamsey.Girth.LabelledBergeCycle.child_has_second_occurrence_of_singleton_intersections
#print axioms StructuralRamsey.Girth.LabelledBergeCycle.child_constant_of_singleton_intersections_twice

#print axioms StructuralRamsey.Girth.FirstWagonRefinement.false_of_short_labelledCycle_in_firstWagon_twice
#print axioms StructuralRamsey.Girth.FirstWagonRefinement.labelledGirthGT_firstWagon_twice
#print axioms StructuralRamsey.Girth.FirstWagonRefinement.girthGT_firstWagon_twice
#print axioms StructuralRamsey.Girth.FirstWagonRefinement.labelledGirthGT_of_first_universal_twice
#print axioms StructuralRamsey.Girth.FirstWagonRefinement.girthGT_of_first_universal_twice
#print axioms StructuralRamsey.Girth.FirstWagonRefinement.labelledGirthGT_of_retainedFirstCut_twice
#print axioms StructuralRamsey.Girth.FirstWagonRefinement.girthGT_of_retainedFirstCut_twice

#print axioms StructuralRamsey.Girth.FirstWagonRefinement.actualSupport_girthGT_of_retainedFirstCut_twice
#print axioms StructuralRamsey.Girth.FirstWagonRefinement.actualSupport_girthGT_of_first_universal_twice

#print axioms StructuralRamsey.Girth.selectedPicture_actualSupport_girthGain_twice_of_fineSystemCuts
#print axioms StructuralRamsey.Girth.selectedPicture_actualSupport_girthGain_twice_of_firstUniversal

#print axioms StructuralRamsey.Girth.BergeCycle.child_constant_of_singleton_intersections_twice
#print axioms StructuralRamsey.Girth.FirstWagonRefinement.actualSupport_girthGT_firstWagon_twice
#print axioms StructuralRamsey.Girth.FirstWagonRefinement.girthGT_heightOne_twice
#print axioms StructuralRamsey.Girth.FirstWagonRefinement.actualSupport_girthGT_heightOne_twice
#print axioms StructuralRamsey.Girth.EdgeTrainLevels.forgetFirstCuts_map_rel_iff
#print axioms StructuralRamsey.Girth.EdgeTrainLevels.forgetFirstCuts_selected_rel_iff
#print axioms StructuralRamsey.Girth.labelledGirthGT_of_singlePartEdgeIntersections
#print axioms StructuralRamsey.Girth.girthGT_of_singlePartEdgeIntersections

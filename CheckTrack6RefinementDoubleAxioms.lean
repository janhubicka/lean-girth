import Girth.TrainRecursivePhysicalFineGirthDouble

set_option autoImplicit false
set_option Elab.async false

/-!
# Track 6 independent strict axiom inspection entrypoint

EXACT-HEAD KERNEL CHECK IS PENDING. This file imports all four
candidate Track 6 modules. The statements below deliberately name
the actual elaborated theorem constants, not source comments or
historical validation markers. A successful run must inspect the
printed axiom sets and reject any sorryAx/unapproved axiom.

Pinned toolchain: leanprover/lean4:v4.35.0-rc3.
Use from repository root:
  LEAN_NUM_THREADS=1 lake env lean CheckTrack6RefinementDoubleAxioms.lean
Or first build imported modules with Lake, then check this file.
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

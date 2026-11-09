import Girth.TrainActualThreeCutFromFullSystem
import Girth.TrainActualGirthFromLengthTwoSource
import Girth.TrainActualSimultaneousSegmentTransfer
import Girth.TrainActualOutputGirthFromOriginalTwo
import Girth.TrainActualBottomReducedTransfer
import Girth.TrainEndpointGeometry
import Girth.UntouchedGirthTransversalBridge

/-!
# Exact interface audit for the proposed simultaneous circulation proof

The first two declarations establish the corrected untouched-fibre
conclusion.  Their existing proof uses the incidence-forest route; they
do not certify the newly written leaf-separator derivation verbatim.

The one-pass declaration expands one fixed reduced supreme plan on the
original occurrence set.  The two-cut declarations cover source length
at least three.  The residual callback interfaces are retained for scope
comparison, and the final declaration closes that callback using the
actual original-length-two source proof.

This file is deliberately at repository root, where the CI axiom loop
discovers Check*.lean.  Run Lean with a successful process exit status,
capture its complete output, and pass that output plus this source to
scripts/check_axioms.py.  The source-correspondence audit is recorded in
notes/SIMULTANEOUS_TRANSFER_VALIDATION_2026-11-09.md.
-/

-- Corrected support-edge transversality; no whole-carrier assertion.
#print axioms StructuralRamsey.Girth.strongSupportPieces_meet_baseFinePartAtMostOne
#print axioms StructuralRamsey.Girth.no_short_untouched_cycle_of_transversal_local_support

-- Literal zero-cut transport retains original labels and complete plans.
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_standard_mappedBigCycle_eq
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_zero_cut_supreme_of_old_bound

-- One fixed reduced plan, expanded simultaneously at three or more cuts.
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_three_cut_one_pass_supreme_of_old_bound
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_three_cut_reduced_supreme_of_fullSystem
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_three_cut_full_supreme_of_old_and_witness

-- Explicit new certificate retains every separated run of the target owner.
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_expanded_plan_keep_iff_target_owner
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_fixed_plan_simultaneous_segment_certificate
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_three_cut_simultaneous_segment_transfer

-- Exactly two cuts with original source length at least three.
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_two_cut_two_standards_full_supreme
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_two_cut_three_le_full_supreme

-- Explicit residual callbacks, not unconditional recursive construction.
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_fullSystemGirth_of_two_cut_cases
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_fullSystemGirth_of_length_two_two_cut

-- Closed local preservation from geometry and ordinary old/witness bounds.
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_fullSystemGirth

-- Bottom forest-to-order uses the chosen reduced plan/bridges alone.
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.length_eq_two_of_order_one
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.connectors_mixed_of_order_one
#print axioms StructuralRamsey.Girth.EdgeTrainLevels.bottom_parent_injective
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_bottom_reduced_supreme
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_bottom_mixed_bridges_supreme

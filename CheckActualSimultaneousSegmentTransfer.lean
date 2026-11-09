import Girth.TrainActualSimultaneousSegmentTransfer

-- Check the physical certificate and its actual full-system transfer.
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_expanded_plan_keep_iff_target_owner
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_fixed_plan_simultaneous_segment_certificate
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_three_cut_simultaneous_segment_transfer

-- Independent long insertions cannot collide, and the single global
-- replacement preserves acceptability, order, and all supreme pullbacks.
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.arbitrary_long_wagons_pairwise
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.arbitrary_resultWord_connectors_nodup
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.arbitrary_replacement_complete_of_three_le

-- Check the original direct proof independently: the shortened argument
-- already has a one-pass implementation in the pinned baseline.
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_three_cut_one_pass_supreme_of_old_bound
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_three_cut_full_supreme_of_old_and_witness

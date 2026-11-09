import Girth.TrainActualExpandedPlanLocalIncidence
import Girth.TrainActualExpandedLongGeometry

/-!
# Simultaneous-transfer segment classification: focused kernel audit

This check follows the at-least-three-cut paragraph of the proposed
`lem:cycletransfer` in girth/paper/12-cycle-preservation.tex.  It audits
existing proofs, without replacing them by weaker geometric assumptions.

Source correspondence:

* A short piece has two actual source contacts. Physical edge locality
  gives adjacency; the canonical order of at least three cuts excludes
  the reverse orientation. The original run is therefore singleton.
* A non-singleton long piece has an old source wagon by source A3.
  Global legality of the SAME specified reduced plan makes that wagon
  fresh at every retained cut, hence uncut. Source A2 locates the two
  boundary vertices on either side of it. The reverse-orientation
  exclusion rules out the complementary two-occurrence arc.
* Exact reverse run fibres show that the resulting run has precisely
  its one or two stated occurrences, including last-to-first wrap.
  The two-occurrence expansion uses two shorts and retains the old wagon.
* The actual expanded source plan has physical incidence at EVERY
  original occurrence. Its only long insertions are singleton runs,
  with globally fresh wagons and the ambient no-pair-edge A2 geometry.

The formal proof classifies singleton/non-singleton runs first, whereas
the manuscript classifies fresh/old wagons first. The fixed-plan two-step
theorem and singleton-long freshness theorem give the two implications
needed to identify these cases. No new selected plan, owner-cut descent,
or designated-occurrence descent occurs in this segment argument.

Run after building the imported modules:

    lake env lean CheckSimultaneousSegmentClassification.lean

Check the captured output with the repository's scripts/check_axioms.py,
passing this file as its second argument. This checks the complete
transitive logical-axiom closure of every declaration listed below.
-/

-- Short pieces: actual source contacts, adjacency, and forward singleton.
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_short_original_cut_contacts
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_reduced_short_cuts_adjacent
#print axioms StructuralRamsey.Girth.cyclicOwnerCutIndex_pred_ne_reverse_succ_of_three_cuts
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_reduced_short_forces_singleton_three_cuts
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_any_plan_nontarget_nonsingleton_is_long

-- Old long wagons: same fixed plan, uncutness, and correct cyclic orientation.
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_long_cut_piece_wagon_is_old_connector
#print axioms StructuralRamsey.Girth.cyclicOwnerCutIndex_no_reverse_single_uncut_gap_of_three_cuts
#print axioms StructuralRamsey.Girth.cyclicOwnerCutIndex_old_uncut_straddle_forward_of_three_cuts
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_long_nonadjacent_two_step_of_cut_fresh
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_fixed_plan_long_nonadjacent_two_step
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_fixed_plan_nontarget_nonadjacent_two_step

-- Exact original occurrence coverage, including wrap and old-wagon retention.
#print axioms StructuralRamsey.Girth.cyclicOwnerRunIndex_singleton_fibre
#print axioms StructuralRamsey.Girth.cyclicOwnerRunIndex_two_step_fibre
#print axioms StructuralRamsey.Girth.cyclicExpandReducedPieces_long_singleton
#print axioms StructuralRamsey.Girth.cyclicExpandReducedPieces_long_two_step
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.expanded_run_plan_localIncidence
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_expanded_plan_localPieceIncidence

-- Only fresh singleton long pieces survive as long insertions in the source.
#print axioms StructuralRamsey.Girth.cyclicExpandReducedPieces_long_inverse
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_plan_long_fresh_of_three_cuts
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_expanded_plan_localLongA2Geometry
#print axioms StructuralRamsey.Girth.attachedSelectedPicture_expanded_plan_long_fresh

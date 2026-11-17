import Girth.Track1FullSelectedWitnessEmbeddings
import Girth.Track1PhysicalActualSelectedIntersections
import Girth.Track1PhysicalFamilyActualMixedLF2
import Girth.Track1TriangleFreePhysicalFamily
import Girth.Track1ActualSelectedCoverage
import Girth.Track1EHNColouredPresentation

/-!
# Numbered Track 1: actual selected-coloured EHN and mixed-LF2 adapters

These source-level candidates must be ELABORATED against the exact
pinned Lake graph. The following axioms must be the standard Lean
logical axioms only. The separate selected-witness staging PR #1074
is an upstream dependency, not an additional assumption.

Even a green check here is NOT the full paper's cutoff-three
partite lemma; true-active picture/fusion is a separate step.
-/

set_option autoImplicit false

#print axioms StructuralRamsey.Girth.track1_aEmbedding_factor_of_carrier_subset
#print axioms StructuralRamsey.Girth.track1_commonA_is_selectedSourceEdge_both
#print axioms StructuralRamsey.Girth.track1_controlled_selectedPhysicalIntersections
#print axioms StructuralRamsey.Girth.track1_forbiddenDegreeOne_of_allowedIntersections
#print axioms StructuralRamsey.Girth.track1_selectedForbiddenDegreeOne
#print axioms StructuralRamsey.Girth.track1_actualSelectedLiftPairwiseAllowed
#print axioms StructuralRamsey.Girth.track1_physicalActualSelectedLiftPairwiseAllowed
#print axioms StructuralRamsey.Girth.track1_oldSelectedColouredOrderedEmbedding
#print axioms StructuralRamsey.Girth.oldColourOfRel_on_selected
#print axioms StructuralRamsey.Girth.track1_oldSelectedEHNColouredEmbedding
#print axioms StructuralRamsey.Girth.track1_exists_actualSelectedColouredLifts
#print axioms StructuralRamsey.Girth.track1_physicalSelectedFamily_actualMixedLF2
#print axioms StructuralRamsey.Girth.track1_physicalRepresentative_supportPieces_injective
#print axioms StructuralRamsey.Girth.track1_physicalRepresentative_arrow
#print axioms StructuralRamsey.Girth.track1_triangleFreeRamsey_physicalSelectedFamily
#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.selectedLiftCarrierFor_covers_splitEdge
#print axioms StructuralRamsey.Girth.track1_actualSelectedOldEdge_covered
#print axioms StructuralRamsey.Girth.track1_actualSelectedSplitEdges_covered

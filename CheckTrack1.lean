import Girth.Track1TriangleFreeSelectedFamily
import Girth.Track1CutoffThreeReuse
import Girth.Track1OwnerSelectedFromEmbedding
import Girth.Track1OwnerSplitGirth
import Girth.Track1OwnerSplitOrderArrow

/-!
# Focused numbered Track 1 validation entrypoint

This is deliberately NOT imported by Girth.lean. It must be built with
`lake env lean CheckTrack1.lean` on the exact candidate head.
Success certifies elaboration of the imported files; the output of the
following #print axioms commands must ALSO be inspected. In particular
the existing external functional EHN dependency is allowed, while
sorryAx or unexpected new axioms are not.

The full manuscript Track 1 conclusion is NOT asserted in this file:
picture-attachment and backward-fusion adapters remain separate.
-/

set_option autoImplicit false

#print axioms StructuralRamsey.Girth.track1_supportCopies_freeAmalgam_union
#print axioms StructuralRamsey.Girth.track1_crossSupport_intersection_common
#print axioms StructuralRamsey.Girth.girthGT_three_union_of_strong_overlap
#print axioms StructuralRamsey.Girth.track1_rightCopy_reflect_left
#print axioms StructuralRamsey.Girth.track1_leftCopy_reflect_right
#print axioms StructuralRamsey.Girth.track1_girthGT_three_freeAmalgam_of_aStrong
#print axioms StructuralRamsey.Girth.ElementaryCAThreeClass_freeAmalgamationClass
#print axioms StructuralRamsey.Girth.track1_selectedOrderedRamseyFamily_triangleFree
#print axioms StructuralRamsey.Girth.track1_three_boundaries_forest_of_core
#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.splitPhysicalEdges_girthGT
#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.selectedLiftEdges_subset_carrier
#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.selectedLiftEdges_eq_splitPhysicalEdges
#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.track1_selectedOrder_and_edgeRamsey
#print axioms StructuralRamsey.Girth.ColouredOwnerSelectedCopy.ofEdgeEmbedding

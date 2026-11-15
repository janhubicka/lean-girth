import Girth.Track1FullSelectedOrderedLifts
import Girth.Track1FullSelectedSupportPieces
import Girth.Track1ActualSelectedOwnerColourArrow

/-!
# Staged Track 1 selected witness integration checks

These are the conditional genuine selected-copy extraction theorems.
Each theorem must elaborate on this exact head, and its printed axioms
must contain no unexpected axiom or sorryAx. The full manuscript theorem
and picture fusion are NOT claimed here.

Staged independently of PR #1069's running kernel CI.
-/

set_option autoImplicit false

#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.exists_commonOrder_fullSelectedLifts
#print axioms StructuralRamsey.Girth.ColouredOwnerSelectedCopy.selectedLiftSupport_allowed
#print axioms StructuralRamsey.Girth.ColouredOwnerSelectedCopy.selectedLiftSupport_pairwiseAllowed
#print axioms StructuralRamsey.Girth.selectedSupportEdges_colourArrow
#print axioms StructuralRamsey.Girth.selectedSupportEdge_image_mem
#print axioms StructuralRamsey.Girth.actualSelectedOwnerCopy
#print axioms StructuralRamsey.Girth.actualSelectedOwner_oldColourArrow

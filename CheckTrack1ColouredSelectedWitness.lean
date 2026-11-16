import Girth.Track1ColouredSelectedWitnessAssembly

/-!
# Exact-head Track 1 selected coloured-witness assembly

This focused checker is for a conditional end-to-end assembly of
the selected local witness, NOT the recursive partite m=3 theorem.
The selected EHN family is an explicit mathematical input.

Success means kernel elaboration and these exact printed axiom sets
have passed the repository's strict scripts/check_axioms.py gate.
-/

set_option autoImplicit false

#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.selectedLiftCarrierFor_covers_splitEdge
#print axioms StructuralRamsey.Girth.track1_actualSelectedOldEdge_covered
#print axioms StructuralRamsey.Girth.track1_actualSelectedSplitEdges_covered
#print axioms StructuralRamsey.Girth.track1_actualSelectedBStrong_from_old
#print axioms StructuralRamsey.Girth.track1_selectedColouredWitness_from_EHN_family

import Girth.TrainFillingPrivateRawOrderObstruction
import Girth.TrainFillingPrivateCompletedOrderedW

set_option Elab.async false

/-!
Track 5: isolated negative check for the difference between
the auxiliary LinearOrder of a raw relational disjoint union
and the actual binary within-colour order relation.

Expected: both theorems elaborate without sorry/axiom.
This gate is NOT a certificate until run on exact-head Lean.
-/

#check StructuralRamsey.Girth.rawFirstWagonUnion_no_cross_order
#check StructuralRamsey.Girth.rawFirstWagonUnion_not_embeddable_in_full_order
#print axioms StructuralRamsey.Girth.rawFirstWagonUnion_no_cross_order
#print axioms StructuralRamsey.Girth.rawFirstWagonUnion_not_embeddable_in_full_order

#check StructuralRamsey.Girth.taggedFirstWagonEdges
#check StructuralRamsey.Girth.completedFirstWagonColouredUnion
#check StructuralRamsey.Girth.completedFirstWagon_edge_in_one_summand
#check StructuralRamsey.Girth.completedFirstWagon_cross_order
#print axioms StructuralRamsey.Girth.completedFirstWagon_edge_in_one_summand
#print axioms StructuralRamsey.Girth.completedFirstWagon_cross_order

#check StructuralRamsey.Girth.completedFirstWagon_edge_of_local
#print axioms StructuralRamsey.Girth.completedFirstWagon_edge_of_local

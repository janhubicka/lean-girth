import Girth.TrainFillingPrivateRawOrderObstruction

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

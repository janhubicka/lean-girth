import Girth.ForestTraceLeafCharging

/-!
Track 8 exact-head Lean gate for the leaf-private charging component.
This file deliberately does not assert that the small-trace theorem
itself is closed.  Run with the pinned project toolchain and inspect
all printed axioms before promoting a validation mark.
-/

#check StructuralRamsey.Girth.JoinTree.exists_leaf_private_vertex
#check StructuralRamsey.Girth.JoinTree.exists_injective_representatives
#check StructuralRamsey.Girth.JoinTree.card_le_of_antichain

#print axioms StructuralRamsey.Girth.JoinTree.exists_leaf_private_vertex
#print axioms StructuralRamsey.Girth.JoinTree.exists_injective_representatives
#print axioms StructuralRamsey.Girth.JoinTree.card_le_of_antichain

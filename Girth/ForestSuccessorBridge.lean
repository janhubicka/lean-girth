import Girth.ForestFreshCarrier
import SuccessorTree.FreeAncestralFiniteRamsey
import SuccessorTree.ShapeEvents

/-!
# Certified successor-tree Ramsey input for the girth-five forest project

The finite hypergraph carrier lemmas are already in `Girth.ForestFreshCarrier`.
This module checks that the free ancestral SMTree and finite shape Ramsey
theorem can be used directly in the girth formalization.

The additional addressed-evaluation and bounded-presentation lemmas of the
forest partite proof are intentionally *not* asserted here.
-/

namespace StructuralRamsey.Girth

universe u w

variable {Label : Type u} [Fintype Label] [Nonempty Label]

/-- The concrete free history tree is an SMTree without auxiliary
pigeonhole or duplication assumptions. -/
noncomputable def forestHistorySMTree (arity : Nat) :
    SuccessorTree.SMTree
      (SuccessorTree.FreeAncestral.freeSTree
        (Label := Label) (arity := arity)) :=
  SuccessorTree.FreeAncestral.freeSMTree

/-- Finite-dimensional homogeneity available for every bounded ancestral
successor-label alphabet.  In the application, labels include the finite
base projection/port roles and two neutral waiting labels. -/
theorem forestHistoryFiniteRamsey
    (arity n k : Nat) {κ : Type w} [Fintype κ]
    (colour :
      SuccessorTree.SMTree.AM
        (forestHistorySMTree (Label := Label) arity) n k → κ) :
    ∃ W :
        SuccessorTree.SMTree.ShapeSubspace
          (forestHistorySMTree (Label := Label) arity) n,
      ∀ a b :
          SuccessorTree.SMTree.AM
            (forestHistorySMTree (Label := Label) arity) n k,
        colour
          ((forestHistorySMTree (Label := Label) arity).shapeActK
            n k W a) =
        colour
          ((forestHistorySMTree (Label := Label) arity).shapeActK
            n k W b) := by
  exact
    (forestHistorySMTree (Label := Label) arity).shapePreservingRamsey
      n k colour

end StructuralRamsey.Girth

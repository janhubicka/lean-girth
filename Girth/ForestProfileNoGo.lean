import Girth.ForestObservableProfile
import Girth.ForestSuccessorBridge

/-!
# Full profile equivariance is incompatible with nontrivial shape colourings

A globally injective map of the evaluated vertex universe preserves the
complete equality profile of marked B-copies. If every shape reduction
were induced by such a map on all marked copies, the resulting profile
colour would be invariant under every shape reduction.

The verified finite successor-tree Ramsey theorem shows that any such
invariant finite colouring is *already constant*. Hence a nontrivial
family of retrospective intersection profiles cannot be modeled by
a fully equivariant ambient embedding action. Only the intrinsic
carrier identities may be required to transport faithfully.

This is a necessary condition on a prospective geometric evaluation,
not an existence theorem for one.
-/

namespace StructuralRamsey.Girth

universe u w

variable {Label : Type u} [Fintype Label] [Nonempty Label]

/-- In a finite-dimensional Ramsey shape action, invariance under every
shape reduction forces a finite colouring to have just one colour on
all finite approximations. -/
theorem forestInvariantProfileColour_constant
    (arity n k : ℕ) {κ : Type w} [Fintype κ]
    (colour :
      SuccessorTree.SMTree.AM
        (forestHistorySMTree (Label := Label) arity) n k → κ)
    (hEquivariant :
      ∀ (W : SuccessorTree.SMTree.ShapeSubspace
          (forestHistorySMTree (Label := Label) arity) n)
        (a : SuccessorTree.SMTree.AM
          (forestHistorySMTree (Label := Label) arity) n k),
        colour
          ((forestHistorySMTree (Label := Label) arity).shapeActK
            n k W a) = colour a) :
    ∀ a b : SuccessorTree.SMTree.AM
        (forestHistorySMTree (Label := Label) arity) n k,
      colour a = colour b := by
  obtain ⟨W, hW⟩ :=
    forestHistoryFiniteRamsey (Label := Label) arity n k colour
  intro a b
  calc
    colour a =
        colour
          ((forestHistorySMTree (Label := Label) arity).shapeActK
            n k W a) := (hEquivariant W a).symm
    _ =
        colour
          ((forestHistorySMTree (Label := Label) arity).shapeActK
            n k W b) := hW a b
    _ = colour b := hEquivariant W b

/-- Equivalently, two different profile colours witness failure of
complete equivariance under the shape action. -/
theorem forestDistinctProfiles_not_fullyEquivariant
    (arity n k : ℕ) {κ : Type w} [Fintype κ]
    (colour :
      SuccessorTree.SMTree.AM
        (forestHistorySMTree (Label := Label) arity) n k → κ)
    (a b : SuccessorTree.SMTree.AM
        (forestHistorySMTree (Label := Label) arity) n k)
    (hab : colour a ≠ colour b) :
    ¬ ∀ (W : SuccessorTree.SMTree.ShapeSubspace
          (forestHistorySMTree (Label := Label) arity) n)
        (x : SuccessorTree.SMTree.AM
          (forestHistorySMTree (Label := Label) arity) n k),
        colour
          ((forestHistorySMTree (Label := Label) arity).shapeActK
            n k W x) = colour x := by
  intro hInv
  exact hab
    (forestInvariantProfileColour_constant
      (Label := Label) arity n k colour hInv a b)

end StructuralRamsey.Girth

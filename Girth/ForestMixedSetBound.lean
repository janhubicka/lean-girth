import Girth.Forest
import Mathlib.Data.Fintype.Basic

/-!
# The old mixed forest bound is a statement about SETS of pieces

The circulation manuscript assumes every set of at most q designated
B-supports and ambient one-A-edge members is a forest. In Lean, the
`ForestOfCopies` predicate is indexed by labels. Arbitrarily
duplicating a multi-edge B-support is not legitimate, so the old
property must NOT be silently applied to a request list containing
equal pieces under different labels.

Take the finite IMAGE of the requested pieces, apply the old forest
bound to its subtype of distinct values, and only then restore
duplicate ONE-EDGE connector labels by permitted leaf attachments.
The latter step is separate (ForestDuplicateOneEdge).
-/

namespace StructuralRamsey.Girth

universe v
variable {W J : Type v}

/-- Faithful set-valued mixed forest property: every finite SET
of permitted support pieces of cardinal at most m forms a forest.
Its indices are the distinct members of that set, not an arbitrary
possibly noninjective list. -/
def FiniteMixedForestThrough
    (tested : HypergraphPiece W → Prop) (m : ℕ) : Prop :=
  ∀ (s : Finset (HypergraphPiece W)),
    (∀ P : HypergraphPiece W, P ∈ s → tested P) →
    s.card ≤ m →
      ForestOfCopies
        (fun P : {P : HypergraphPiece W // P ∈ s} => P.1)

/-- A labelled family of at most m tested pieces gives a forest
on its DISTINCT image pieces. No foresthood of the possibly
duplicated original labels is claimed. -/
theorem FiniteMixedForestThrough.image
    [Fintype J]
    (tested : HypergraphPiece W → Prop) (m : ℕ)
    (hProperty : FiniteMixedForestThrough tested m)
    (F : J → HypergraphPiece W)
    (hTest : ∀ j : J, tested (F j))
    (hCount : Fintype.card J ≤ m) :
    ForestOfCopies
      (fun P : {P : HypergraphPiece W // P ∈
        (Finset.univ.image F)} => P.1) := by
  classical
  apply hProperty (Finset.univ.image F)
  · intro P hP
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hP
    exact hTest j
  · calc
      (Finset.univ.image F).card ≤ (Finset.univ : Finset J).card :=
        Finset.card_image_le
      _ = Fintype.card J := Finset.card_univ
      _ ≤ m := hCount

end StructuralRamsey.Girth

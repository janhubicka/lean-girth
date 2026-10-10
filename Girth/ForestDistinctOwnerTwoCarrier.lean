import Girth.ForestDistinctOwnersGirthOnly
import Girth.ForestOverlapTransfer

/-!
# The two-carrier bridge for the distinct-owner forest increment

Actual selected A/B support pieces live in FULL standard pictures,
while pairwise overlaps of different standard pictures occur in the
SMALL local gluing pieces. The exact overlap identity, together
with containment of each small piece in the local core, implies
the cross-owner core-intersection premise required by the
girth-only all-distinct forest theorem.

This is a structural bridge: no separate outer join tree or
local forest family is needed in the pairwise distinct-owner case.
The exact boundary dichotomy for each selected A/B support piece
still comes from the active-boundary classification.
-/

namespace StructuralRamsey.Girth

universe v
variable {W N Q : Type v}

/-- Distinct selected full-standard owners with exact gluing
overlaps give a forest as soon as the local support has girth
above q and every selected piece has its own small-or-whole
boundary support. -/
theorem selectedForest_of_distinctOwners_twoCarrier
    [Fintype N] [Nonempty N]
    (selected : N → HypergraphPiece W)
    (owner : N → Q)
    (hOwnerInj : Function.Injective owner)
    (small full : Q → HypergraphPiece W)
    (S : Set W) [Fintype S]
    (K : Set (Set W)) (q : ℕ)
    (hq : 2 ≤ q)
    (hSelectedCard : Fintype.card N ≤ q)
    (hGirth : GirthGT K q)
    (hOverlap :
      ∀ ⦃a b : Q⦄, a ≠ b →
        (full a).carrier ∩ (full b).carrier =
          (small a).carrier ∩ (small b).carrier)
    (hSmallCore : ∀ a : Q, (small a).carrier ⊆ S)
    (hSelectedContained :
      ∀ i : N, (selected i).carrier ⊆
        (full (owner i)).carrier)
    (hBoundary :
      ∀ i : N, SmallOrWholeEdgeBoundary K S (selected i)) :
    ForestOfCopies selected := by
  have hCross :
      ∀ ⦃i j : N⦄, i ≠ j →
        (selected i).carrier ∩ (selected j).carrier ⊆ S := by
    intro i j hij x hx
    have hDifferent : owner i ≠ owner j :=
      hOwnerInj hij
    have hxFull :
        x ∈ (full (owner i)).carrier ∩
          (full (owner j)).carrier :=
      ⟨hSelectedContained i hx.1,
        hSelectedContained j hx.2⟩
    have hxSmall :
        x ∈ (small (owner i)).carrier ∩
          (small (owner j)).carrier := by
      rw [← hOverlap hDifferent]
      exact hxFull
    exact hSmallCore (owner i) hxSmall.1
  exact selectedForest_of_distinctOwners_girthOnly
    selected S K q hq hSelectedCard hGirth
    hBoundary hCross

end StructuralRamsey.Girth

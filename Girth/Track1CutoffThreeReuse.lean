import Girth.ForestDistinctOwnersGirthOnly
import Mathlib.Tactic

/-!
# Track 1: reuse existing all-distinct forest theorem at cutoff three

The full general theorem is already in the library. This is an exact
hypothesis-level adapter for the manuscript's lem:threeboundaries.
DRAFT: no exact-head kernel check. Actual picture geometry is separate.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- At most three distinct pieces whose intersections lie in the finite core,
with exact small/whole-edge boundaries, form a forest under girth >3. -/
theorem track1_three_boundaries_forest_of_core
    [Fintype I] [Nonempty I]
    (selected : I → HypergraphPiece W)
    (S : Set W) [Fintype S]
    (K : Set (Set W))
    (hCard : Fintype.card I ≤ 3)
    (hCoreGirth : GirthGT K 3)
    (hBoundary : ∀ i : I,
      SmallOrWholeEdgeBoundary K S (selected i))
    (hCross : ∀ ⦃i j : I⦄, i ≠ j →
      (selected i).carrier ∩ (selected j).carrier ⊆ S) :
    ForestOfCopies selected := by
  exact selectedForest_of_distinctOwners_girthOnly
    selected S K 3 (by omega) hCard hCoreGirth
    hBoundary hCross

#print axioms StructuralRamsey.Girth.track1_three_boundaries_forest_of_core

end StructuralRamsey.Girth

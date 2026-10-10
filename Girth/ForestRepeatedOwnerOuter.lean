import Girth.ForestOwnerInjectiveSplit
import Girth.ForestUsedOwnerLocalForest
import Girth.ForestOverlapTransfer

/-!
# Previous-cutoff outer forest when selected owners repeat

In the repeated-owner branch of the direct circulation forest increment,
the number of distinct gluing owners is at most q-1. Hence the local
witness needs bounded foresthood only through q-1, not through q.
Pairwise equality of small-gluing and full-standard intersections then
transfers that outer forest to the full standard pictures, without
identifying their private vertices or edges.

This theorem establishes exactly the outer forest needed by the
subsequent join-tree lift. Owner-wise selected and connector members,
their old-picture q-budget, and removal of one-edge auxiliary members
remain separate steps.
-/

namespace StructuralRamsey.Girth

universe v
variable {N I W : Type v}

/-- Repeated owners reduce the chosen local gluing family to the
previous cutoff, with no global foresthood assumption on all gluing copies. -/
theorem localForest_repeatedOwners
    [Fintype N] (owner : N → I)
    (small : I → HypergraphPiece W) (q : ℕ)
    (hCount : Fintype.card N ≤ q)
    (hNoninjective : ¬ Function.Injective owner)
    (hPrevious : LocalForestThrough small (q - 1)) :
    ForestOfCopies
      (fun i : UsedOwner owner => small i.1) := by
  classical
  letI : Fintype (UsedOwner owner) := usedOwnerFintype owner
  let incl : UsedOwner owner ↪ I :=
    ⟨Subtype.val, Subtype.val_injective⟩
  exact hPrevious (UsedOwner owner) incl
    (usedOwner_card_le_prev_of_not_injective
      owner q hCount hNoninjective)

/-- The full standard pictures of the ACTUALLY USED owners form a forest
as soon as their overlaps equal the overlaps of the smaller gluing pieces.
No false hereditary-subfamily assertion is made. -/
theorem fullStandardForest_repeatedOwners
    [Fintype N] (owner : N → I)
    (small full : I → HypergraphPiece W) (q : ℕ)
    (hCount : Fintype.card N ≤ q)
    (hNoninjective : ¬ Function.Injective owner)
    (hPrevious : LocalForestThrough small (q - 1))
    (hCarrier : ∀ i, (small i).carrier ⊆ (full i).carrier)
    (hEdges : ∀ i, (small i).edges ⊆ (full i).edges)
    (hPair : ∀ ⦃i j : I⦄, i ≠ j →
      (full i).carrier ∩ (full j).carrier =
        (small i).carrier ∩ (small j).carrier) :
    ForestOfCopies
      (fun i : UsedOwner owner => full i.1) := by
  have hSmall :
      ForestOfCopies
        (fun i : UsedOwner owner => small i.1) :=
    localForest_repeatedOwners owner small q
      hCount hNoninjective hPrevious
  apply hSmall.transfer_of_pair_intersections
    (fun i => hCarrier i.1)
  · intro a b hab
    have hDistinct : a.1 ≠ b.1 := by
      intro h
      exact hab (Subtype.ext h)
    exact hPair hDistinct
  · exact fun i => hEdges i.1

end StructuralRamsey.Girth

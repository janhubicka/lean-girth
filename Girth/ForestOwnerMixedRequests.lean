import Girth.ForestMixedSetBound
import Girth.CompletionBudget

/-!
# Exact q-budget for the DISTINCT old-picture local requests

At an outer join-tree owner q, the request labels are selected
members assigned to q plus one temporary one-edge separator
request for every neighbouring owner. The total number of labels
is at most the original selected-family size, thanks to the
surjective owner map and the tree degree bound.

The old picture's MIXED forest property applies to the DISTINCT
IMAGE of these requests. It does not automatically apply to the
labelled list when a one-edge separator occurs more than once;
that subsequent clone-insertion step is separate.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q N : Type v}

/-- Apply the genuine set-valued old mixed q-forest property to
each owner's distinct selected-plus-neighbour request image,
using the sharp fiber-size-plus-tree-degree bound. -/
theorem FiniteMixedForestThrough.distinctOwnerRequests
    [Fintype Q] [DecidableEq Q] [Fintype N]
    (owner : N → Q) (hSurj : Function.Surjective owner)
    (G : SimpleGraph Q) [DecidableRel G.Adj]
    (m : ℕ) (hSelectedCount : Fintype.card N ≤ m)
    (tested : HypergraphPiece W → Prop)
    (hOld : FiniteMixedForestThrough tested m)
    (selected : N → HypergraphPiece W)
    (hSelectedTest : ∀ n, tested (selected n))
    (separator : (q : Q) → G.neighborSet q → HypergraphPiece W)
    (hSeparatorTest : ∀ q r, tested (separator q r))
    (q : Q) :
    let requests :
      ({n : N // owner n = q} ⊕ G.neighborSet q) →
        HypergraphPiece W :=
      fun z => match z with
        | .inl n => selected n.1
        | .inr r => separator q r
    ForestOfCopies
      (fun P : {P : HypergraphPiece W // P ∈
          Finset.univ.image requests} => P.1) := by
  classical
  let requests :
      ({n : N // owner n = q} ⊕ G.neighborSet q) →
        HypergraphPiece W :=
    fun z => match z with
      | .inl n => selected n.1
      | .inr r => separator q r
  have hBound :
      Fintype.card ({n : N // owner n = q} ⊕ G.neighborSet q) ≤ m := by
    rw [Fintype.card_sum, G.card_neighborSet_eq_degree q]
    exact (ownerFiber_card_add_degree_le owner hSurj G q).trans hSelectedCount
  have hTest :
      ∀ z : ({n : N // owner n = q} ⊕ G.neighborSet q),
        tested (requests z) := by
    intro z
    cases z with
    | inl n => exact hSelectedTest n.1
    | inr r => exact hSeparatorTest q r
  exact hOld.image tested m requests hTest hBound

end StructuralRamsey.Girth

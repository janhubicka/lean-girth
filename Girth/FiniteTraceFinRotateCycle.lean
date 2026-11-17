import Girth.FiniteTraceSuccessorCycle
import Mathlib.GroupTheory.Perm.Fin

/-!
# Finite rotation version of the chordless-cycle obstruction

The preceding generic successor-permutation lemma is specialised to
the usual cyclic order on Fin k using Mathlib's *existing* finRotate.
Its bijectivity is supplied by finRotate itself, not reproved using
ad hoc modular arithmetic.  For k >= 4 there are no fixed points:
Mathlib's theorem support_finRotate_of_le shows every index moves.

A simple induced graph cycle is usually provided as an injective
list of k vertices with consecutive edges and no chord.  The only
remaining concrete cycle adapter is to prove that such a list gives
the CrossPairNonedge data.  No graph chordality theorem is claimed.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- A nontrivial finite rotation has no fixed points. This uses
the exact pinned Mathlib finite-permutation support theorem. -/
theorem finRotate_no_fixed_of_four_le
    {k : ℕ} (hk : 4 ≤ k) :
    ∀ i : Fin k, finRotate k i ≠ i := by
  intro i heq
  have hSupport : (finRotate k).support = Finset.univ :=
    support_finRotate_of_le (by omega : 2 ≤ k)
  have hi : i ∈ (finRotate k).support := by
    rw [hSupport]
    exact Finset.mem_univ i
  exact (Equiv.Perm.mem_support.mp hi) heq

/-- Exact original-cover obstruction for a chordless cycle already
indexed by Fin k, with successor finRotate k.  This wrapper removes
all abstract permutation requirements from the user-facing data. -/
theorem no_bounded_chordless_fin_rotate
    [Fintype ι]
    (F : ι → Set W) (Z : Set W) (q k : ℕ)
    (hLocal : HasInternalJoinTreeCompletions F q)
    (hk : 4 ≤ k)
    (hBudget : k ≤ q)
    (v : Fin k → Z)
    (hEdges :
      ∀ i : Fin k,
        (tracePairGraph F Z).Adj (v i) (v (finRotate k i)))
    (hCross :
      ∀ i j : Fin k, i ≠ j →
        CrossPairNonedge (tracePairGraph F Z)
          v (fun z => v (finRotate k z)) i j) :
    False := by
  classical
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hCard : Fintype.card (Fin k) ≤ q := by
    simpa only [Fintype.card_fin] using hBudget
  exact no_bounded_chordless_successor_cycle
    F Z q hLocal (finRotate k)
    (finRotate_no_fixed_of_four_le hk)
    v hCard hEdges hCross

end StructuralRamsey.Girth

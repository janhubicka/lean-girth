import Girth.TrainRecursiveWitness
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Exact cutoff positions in the larger-cutoff recursive call

For a request q :: tail, with q > 2, the lower-rank invocation uses
List.replicate (r + 1) (q - 1) ++ tail. The first r + 1 coordinates
carry the SMALL cutoff q - 1. The first retained tail coordinate lies
at index r + 1 and has a cutoff AT LEAST q, because the original
request is nondecreasing.

The distinction is essential: the physical global girth-gain theorem
needs the stronger retained first-cut bound, which cannot be taken from
an inserted smaller-cutoff coordinate. These are literal list-index
statements; no fictitious train equivalence or recursive witness is
constructed.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

/-- The concrete list entry at every inserted prefix index is exactly
the smaller cutoff. -/
theorem replicatedCutoff_at_inserted
    (g d : ℕ) (tail : List ℕ) (j : Fin d) :
    (List.replicate d g ++ tail).get
      ⟨j.val, by
        simp only [List.length_append, List.length_replicate]
        omega⟩ = g := by
  change (List.replicate d g ++ tail)[j.val] = g
  simp [List.getElem_append, j.isLt]

/-- Every retained tail entry is found at the original tail index plus
the length of the inserted prefix, and retains its original value. -/
theorem replicatedCutoff_at_retained
    (g d : ℕ) (tail : List ℕ) (i : Fin tail.length) :
    (List.replicate d g ++ tail).get
      ⟨d + i.val, by
        simp only [List.length_append, List.length_replicate]
        omega⟩ = tail.get i := by
  change (List.replicate d g ++ tail)[d + i.val] = tail[i.val]
  have h := List.getElem_append_right' (List.replicate d g) i.isLt
  simpa only [List.length_replicate, Nat.add_comm] using h.symm

/-- A monotone original request gives every retained tail coordinate
a cutoff at least the original leading cutoff. -/
theorem replicatedCutoff_retained_ge
    (q g d : ℕ) (tail : List ℕ)
    (hOrder : (q :: tail).Pairwise (· ≤ ·))
    (i : Fin tail.length) :
    q ≤ (List.replicate d g ++ tail).get
      ⟨d + i.val, by
        simp only [List.length_append, List.length_replicate]
        omega⟩ := by
  have hTail : q ≤ tail.get i :=
    (List.pairwise_cons.mp hOrder).1 (tail.get i) (List.get_mem tail i)
  rw [replicatedCutoff_at_retained g d tail i]
  exact hTail

/-- At the first retained tail coordinate of a nonempty tail, the
recursive call has exactly the stronger budget needed for the
q=g+1 global physical girth increment. -/
theorem firstRetainedCutoff_ge_next
    (q g r : ℕ) (tail : List ℕ)
    (hNonempty : tail ≠ [])
    (hOrder : (q :: tail).Pairwise (· ≤ ·))
    (hNext : g + 1 ≤ q) :
    g + 1 ≤ (List.replicate (r + 1) g ++ tail).get
      ⟨r + 1, by
        simp only [List.length_append, List.length_replicate]
        have hn := List.length_pos_iff.mpr hNonempty
        omega⟩ := by
  let i : Fin tail.length := ⟨0, List.length_pos_iff.mpr hNonempty⟩
  have hTail := replicatedCutoff_retained_ge q g (r + 1) tail hOrder i
  simpa [i] using hNext.trans hTail

end StructuralRamsey.Girth.TrainRecursiveWitness

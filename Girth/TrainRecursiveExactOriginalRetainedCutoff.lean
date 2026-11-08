import Girth.TrainRecursiveExactRetainedFullSystemGirth
import Girth.TrainRecursiveCutoffIndexAlignment
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# The retained lower cutoff is EXACTLY the old positive cutoff

When the original vector is q :: tail and the finer local recursive
request replaces q by r+1 copies of q-1, each genuine positive old
cut j (1 <= j < (q::tail).length) corresponds to fine cut j+r.

At this literal fine index the lower list contains exactly the old
value (q::tail).get j, NOT merely the uniform lower bound q. This
distinction is essential for the positive attached tail supreme
certificate when the original tail increases.

The proof is arithmetic on lists and original indices only. It
neither constructs nor assumes a girth certificate and does not
alter physical edges, selected labels or wagon quotients.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

/-- Every positive old position j is a genuine retained tail slot,
and its cutoff matches the literal lower list entry after the r
inserted first-wagon cuts. -/
theorem originalPositiveCutoff_eq_lowerRetained
    (q r : ℕ) (tail : List ℕ)
    (j : Fin (q :: tail).length) (hj : 0 < j.val) :
    (List.replicate (r + 1) (q - 1) ++ tail).get
      ⟨j.val + r, by
        have hjLt := j.isLt
        simp only [List.length_cons] at hjLt
        simp only [List.length_append, List.length_replicate]
        omega⟩ =
      (q :: tail).get j := by
  let k : Fin tail.length := ⟨j.val - 1, by
    have hlt := j.isLt
    simp only [List.length_cons] at hlt
    omega⟩
  have hjEq : j = (Fin.succ k : Fin (q :: tail).length) := by
    apply Fin.ext
    change j.val = (j.val - 1) + 1
    omega
  have hIndex :
      (⟨j.val + r, by
        have hlt := j.isLt
        simp only [List.length_cons] at hlt
        simp only [List.length_append, List.length_replicate]
        omega⟩ : Fin (List.replicate (r + 1) (q - 1) ++ tail).length) =
      ⟨(r + 1) + k.val, by
        simp only [List.length_append, List.length_replicate]
        exact Nat.add_lt_add_left k.isLt (r + 1)⟩ := by
    apply Fin.ext
    change j.val + r = (r + 1) + (j.val - 1)
    omega
  rw [hIndex, replicatedCutoff_at_retained (q - 1) (r + 1) tail k]
  rw [hjEq]
  rfl

end StructuralRamsey.Girth.TrainRecursiveWitness

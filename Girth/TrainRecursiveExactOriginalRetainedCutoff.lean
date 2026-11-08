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
    have hjLt := j.isLt
    simp only [List.length_cons] at hjLt
    omega⟩
  have hIndex : j.val = k.val + 1 := by
    dsimp [k]
    omega
  have hOffset : j.val + r = (r + 1) + k.val := by omega
  have hRetained := replicatedCutoff_at_retained (q - 1) (r + 1) tail k
  change (List.replicate (r + 1) (q - 1) ++ tail)[(r + 1) + k.val] =
    tail[k.val] at hRetained
  change (List.replicate (r + 1) (q - 1) ++ tail)[j.val + r] =
    (q :: tail)[j.val]
  calc
    (List.replicate (r + 1) (q - 1) ++ tail)[j.val + r] =
        (List.replicate (r + 1) (q - 1) ++ tail)[(r + 1) + k.val] := by
      rw [hOffset]
    _ = tail[k.val] := hRetained
    _ = (q :: tail)[j.val] := by
      rw [hIndex]
      simp

end StructuralRamsey.Girth.TrainRecursiveWitness

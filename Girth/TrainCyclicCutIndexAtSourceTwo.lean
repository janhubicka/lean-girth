import Girth.TrainCyclicCutIndices
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: at ORIGINAL source length two, two cuts have no index rotation

A genuine two-occurrence source word with exactly two cyclic owner
changes has BOTH original positions as owner-cut positions. The
checked canonical strictly monotone cut enumerator therefore sends
its two indices to original positions 0 and 1 respectively.

This is a purely finite identity: it does not change any original
source label, assume designatedness or construct a supreme plan.
It removes the otherwise easy-to-miss indexing permutation in the
still-open original n=2 case of the circulation output-girth proof.
No appendix or TeX.
-/

namespace StructuralRamsey.Girth

universe v

/-- With ORIGINAL source length exactly TWO and exactly TWO owner
cuts, the canonical cut-index map is the literal identity on
index values, not an unverified cyclic rotation. -/
theorem cyclicOwnerCutIndex_val_eq_of_source_two
    {Owner : Type v} (owner : Fin 2 → Owner)
    (hTwo : cyclicOwnerChanges owner = 2)
    (j : Fin (cyclicOwnerChanges owner)) :
    (cyclicOwnerCutIndex owner j).val = j.val := by
  let a : Fin (cyclicOwnerChanges owner) := ⟨0, by omega⟩
  let b : Fin (cyclicOwnerChanges owner) := ⟨1, by omega⟩
  have hab : a < b := by
    change (0 : ℕ) < 1
    omega
  have hStrict : cyclicOwnerCutIndex owner a <
      cyclicOwnerCutIndex owner b :=
    (cyclicOwnerCutIndex owner).strictMono hab
  have hAVal : (cyclicOwnerCutIndex owner a).val = 0 := by
    have haBound := (cyclicOwnerCutIndex owner a).isLt
    have hbBound := (cyclicOwnerCutIndex owner b).isLt
    have habVal :
        (cyclicOwnerCutIndex owner a).val <
          (cyclicOwnerCutIndex owner b).val := hStrict
    omega
  have hBVal : (cyclicOwnerCutIndex owner b).val = 1 := by
    have haBound := (cyclicOwnerCutIndex owner a).isLt
    have hbBound := (cyclicOwnerCutIndex owner b).isLt
    have habVal :
        (cyclicOwnerCutIndex owner a).val <
          (cyclicOwnerCutIndex owner b).val := hStrict
    omega
  have hjVal := j.isLt
  by_cases hj0 : j.val = 0
  · have hjEq : j = a := Fin.ext hj0
    rw [hjEq]
    exact hAVal
  · have hj1 : j.val = 1 := by omega
    have hjEq : j = b := Fin.ext hj1
    rw [hjEq]
    exact hBVal

end StructuralRamsey.Girth

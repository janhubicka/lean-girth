import Girth.TrainCyclicRunGaps
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# A cyclic owner word cannot have exactly one change

In the positive-cut supreme-cycle induction we choose a MINIMAL
geometric owner assignment of the actual source cycle. Its number
of changes is either zero or at least two. One single cyclic owner
change is impossible: all other successor links force the two sides
of that putative change to have the same owner after going around
the finite cyclic word.

This is a structural fact about arbitrary owner types, with no
finiteness or decidable equality assumed on the owner type. We use
the actual cut-index enumeration and the previously verified
linear-interval owner-constancy lemma; the wrap edge from the last
position back to zero is included explicitly. No appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- A finite cyclic assignment with at least two positions has
no unique owner change, including at the last-to-first boundary.
The owner type need not be finite. -/
theorem cyclicOwnerChanges_ne_one
    (hn : 2 ≤ n) (owner : Fin n → Owner) :
    cyclicOwnerChanges owner ≠ 1 := by
  intro hone
  have hpos : 0 < cyclicOwnerChanges owner := by omega
  let j : Fin (cyclicOwnerChanges owner) := ⟨0, hpos⟩
  let k : Fin n := cyclicOwnerCutIndex owner j
  let zero : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hDiff : owner k ≠ owner (cyclicSucc k) :=
    cyclicOwnerCutIndex_is_change owner j
  have hNoOther (t : Fin n) (ht : t ≠ k) :
      owner t = owner (cyclicSucc t) := by
    by_contra hBad
    obtain ⟨r, hr⟩ := (cyclicOwnerCutIndex_mem_iff owner t).mp
      ((mem_cyclicOwnerCutPositions_iff owner t).mpr hBad)
    have hrj : r = j := by
      apply Fin.ext
      have hrlt : r.val < cyclicOwnerChanges owner := r.isLt
      change r.val = 0
      omega
    rw [hrj] at hr
    exact ht hr.symm
  have hBefore : owner zero = owner k := by
    apply cyclicOwner_constant_on_linear_interval owner zero k
    · change (0 : ℕ) ≤ k.val
      omega
    · intro t _ ht
      exact hNoOther t (ne_of_lt ht)
  have hSuccLast : cyclicSucc last = zero := by
    apply Fin.ext
    change (n - 1 + 1) % n = 0
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
    exact Nat.mod_self n
  by_cases hLast : k = last
  · rw [hLast] at hBefore
    rw [hLast, hSuccLast] at hDiff
    exact hDiff hBefore.symm
  · have hklt : k.val < n - 1 := by
      have hkn := k.isLt
      have hkNe : k.val ≠ n - 1 := by
        intro heq
        exact hLast (Fin.ext heq)
      omega
    have hSuccK : (cyclicSucc k).val = k.val + 1 := by
      change (k.val + 1) % n = k.val + 1
      exact Nat.mod_eq_of_lt (by omega)
    have hAfter : owner (cyclicSucc k) = owner last := by
      apply cyclicOwner_constant_on_linear_interval owner (cyclicSucc k) last
      · change (cyclicSucc k).val ≤ n - 1
        rw [hSuccK]
        omega
      · intro t hFrom _
        apply hNoOther t
        have hkt : k < t := by
          change k.val < t.val
          have hv : (cyclicSucc k).val ≤ t.val := hFrom
          rw [hSuccK] at hv
          omega
        exact Ne.symm (ne_of_lt hkt)
    have hBack : owner last = owner zero := by
      have h := hNoOther last (Ne.symm hLast)
      rw [hSuccLast] at h
      exact h
    exact hDiff (hBefore.symm.trans (hBack.symm.trans hAfter.symm))

/-- A cyclic owner assignment of a genuine BigCycle is either
constant (no cuts) or has at least TWO cyclic cuts. There is
no hidden intermediate case in the supremeness induction. -/
theorem cyclicOwnerChanges_zero_or_two_le
    (hn : 2 ≤ n) (owner : Fin n → Owner) :
    cyclicOwnerChanges owner = 0 ∨ 2 ≤ cyclicOwnerChanges owner := by
  have hne : cyclicOwnerChanges owner ≠ 1 :=
    cyclicOwnerChanges_ne_one hn owner
  omega

end StructuralRamsey.Girth

import Girth.Berge
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Tuple.Basic

/-! # Runs in a cyclic finite word

A mixed Berge cycle is controlled by the runs of edges lying on one side of
an amalgam.  This file isolates the elementary cyclic-index lemma used by both
singleton and common-edge gluings.
-/

namespace StructuralRamsey.Girth

/-- Our cyclic successor agrees with mathlib's canonical rotation of `Fin n`. -/
theorem cyclicSucc_eq_finRotate {n : ℕ} (i : Fin n) :
    cyclicSucc i = finRotate n i := by
  apply Fin.ext
  simp [cyclicSucc, finRotate_apply, Fin.add_def]

/-- A nonconstant cyclic Boolean word has an adjacent change. -/
theorem exists_cyclic_change_of_nonconstant
    {n : ℕ} (side : Fin n → Bool)
    (hmix : ∃ i j : Fin n, side i ≠ side j) :
    ∃ i : Fin n, side i ≠ side (finRotate n i) := by
  by_contra hnone
  push_neg at hnone
  cases n with
  | zero =>
      rcases hmix with ⟨i, _, _⟩
      exact i.elim0
  | succ n =>
      have hall : ∀ (m : ℕ) (hm : m < n + 1),
          side ⟨m, hm⟩ = side 0 := by
        intro m hm
        induction m with
        | zero => rfl
        | succ m ih =>
            have hmn : m < n := by omega
            have hprev := hnone ⟨m, by omega⟩
            have hrot :
                finRotate (n + 1) ⟨m, by omega⟩ =
                  ⟨m + 1, hm⟩ := by
              simpa using (finRotate_of_lt (n := n) hmn)
            rw [hrot] at hprev
            exact hprev.symm.trans (ih (by omega))
      rcases hmix with ⟨i, j, hij⟩
      apply hij
      exact (hall i.1 i.2).trans (hall j.1 j.2).symm

/-- Every nonempty finite Boolean word has a maximal constant prefix.
The prefix ends either at the end of the word or immediately before its first
change. -/
theorem exists_constant_prefix
    {n : ℕ} (hn : 0 < n) (side : Fin n → Bool) :
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧
      (∀ m : ℕ, m < k →
        side ⟨m, lt_of_lt_of_le ‹m < k› ‹k ≤ n›⟩ = side 0) ∧
      (k = n ∨ ∃ hk : k < n, side ⟨k, hk⟩ ≠ side 0) := by
  let p : Fin n → Prop := fun i => side i ≠ side 0
  letI : DecidablePred p := Classical.decPred p
  by_cases hex : ∃ i : Fin n, p i
  · let kf : Fin n := Fin.find p hex
    have hkSpec : p kf := Fin.find_spec hex
    have hkpos : 0 < kf.1 := by
      by_contra hk
      have hk0 : kf = 0 := Fin.ext (by omega)
      subst kf
      simpa [p] using hkSpec
    refine ⟨kf.1, hkpos, Nat.le_of_lt kf.2, ?_, Or.inr ⟨kf.2, hkSpec⟩⟩
    intro m hm
    let mf : Fin n := ⟨m, lt_trans hm kf.2⟩
    have hmf : mf < kf := hm
    have hnot : ¬ p mf := Fin.find_min hex hmf
    exact not_ne_iff.mp hnot
  · refine ⟨n, hn, le_rfl, ?_, Or.inl rfl⟩
    intro m hm
    have hnot : ¬ p ⟨m, hm⟩ := by
      intro hp
      exact hex ⟨⟨m, hm⟩, hp⟩
    exact not_ne_iff.mp hnot

/-- Starting immediately after a change in a cyclic Boolean word, there is a
first later change before returning all the way around the circle.  Thus the
intervening positive-length block is constant. -/
theorem exists_first_cyclic_change
    {n : ℕ} (hn : 2 ≤ n) (side : Fin n → Bool) (before : Fin n)
    (hchange : side before ≠ side (finRotate n before)) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧
      side (finCycle ⟨k, by omega⟩ (finRotate n before)) ≠
        side (finRotate n before) ∧
      ∀ m : ℕ, m < k →
        side (finCycle ⟨m, by omega⟩ (finRotate n before)) =
          side (finRotate n before) := by
  let start : Fin n := finRotate n before
  let p : Fin n → Prop := fun k => side (finCycle k start) ≠ side start
  letI : DecidablePred p := Classical.decPred p
  have hex : ∃ k : Fin n, p k := by
    refine ⟨-1, ?_⟩
    have hback : finCycle (-1 : Fin n) start = before := by
      dsimp [start]
      simp [finCycle_apply, finRotate_apply, add_assoc]
    rw [p, hback]
    exact hchange
  let k : Fin n := Fin.find p hex
  have hkSpec : p k := by
    exact Fin.find_spec hex
  have hkpos : 0 < k.1 := by
    by_contra hk
    have hk0 : k = 0 := Fin.ext (by omega)
    subst k
    simpa [p, start, finCycle_apply] using hkSpec
  refine ⟨k.1, hkpos, k.2, ?_, ?_⟩
  · exact hkSpec
  · intro m hm
    let mf : Fin n := ⟨m, lt_trans hm k.2⟩
    have hmf : mf < k := by
      exact hm
    have hnot : ¬ p mf := Fin.find_min hex hmf
    exact not_ne_iff.mp hnot

end StructuralRamsey.Girth

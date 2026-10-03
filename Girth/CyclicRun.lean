import Girth.Berge
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Tuple.Basic

/-! # Runs in a cyclic finite word

A mixed Berge cycle is controlled by the runs of edges lying on one side of
an amalgam.  This file isolates the elementary cyclic-index lemmas used by the
girth-preservation proof.
-/

namespace StructuralRamsey.Girth

/-- Index obtained by moving `offset` steps from the edge immediately after
`before`. -/
def cyclicRunIndex {n : ℕ} (before offset : Fin n) : Fin n :=
  finCycle offset (finRotate n before)

@[simp]
theorem cyclicRunIndex_zero {n : ℕ} [NeZero n] (before : Fin n) :
    cyclicRunIndex before (0 : Fin n) = finRotate n before := by
  simp [cyclicRunIndex, finCycle_apply]

/-- A proper positive offset after the successor of `before` cannot
return to `before`. -/
theorem cyclicRunIndex_ne_before
    {n : ℕ} (before offset : Fin n)
    (hproper : offset.1 + 1 < n) :
    cyclicRunIndex before offset ≠ before := by
  letI : NeZero n := ⟨by omega⟩
  intro h
  have hEq : before + (1 + offset) = before := by
    simpa [cyclicRunIndex, finCycle_apply, finRotate_apply,
      add_assoc, add_comm, add_left_comm] using h
  have hzero : (1 + offset : Fin n) = 0 := by
    apply add_left_cancel (a := before)
    simpa using hEq
  have hval : ((1 + offset : Fin n) : ℕ) = offset.1 + 1 := by
    rw [Fin.val_add_eq_of_add_lt]
    · rfl
    · simpa [add_comm] using hproper
  have hz := congrArg Fin.val hzero
  rw [hval] at hz
  simp at hz

/-- Our cyclic successor agrees with mathlib's canonical rotation of `Fin n`. -/
theorem cyclicSucc_eq_finRotate {n : ℕ} (i : Fin n) :
    cyclicSucc i = finRotate n i := by
  letI := i.neZero
  apply Fin.ext
  simp [cyclicSucc, finRotate_apply, Fin.add_def]

/-- A nonconstant cyclic Boolean word has an adjacent change. -/
theorem exists_cyclic_change_of_nonconstant
    {n : ℕ} (side : Fin n → Bool)
    (hmix : ∃ i j : Fin n, side i ≠ side j) :
    ∃ i : Fin n, side i ≠ side (finRotate n i) := by
  by_contra hnone
  push Not at hnone
  cases n with
  | zero =>
      rcases hmix with ⟨i, _, _⟩
      exact i.elim0
  | succ n =>
      let z : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
      have hall : ∀ (m : ℕ) (hm : m < n + 1),
          side ⟨m, hm⟩ = side z := by
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

/-- Starting immediately after a change in a cyclic Boolean word, there is a
first later change before returning all the way around the circle. -/
theorem exists_first_cyclic_change
    {n : ℕ} (hn : 2 ≤ n) (side : Fin n → Bool) (before : Fin n)
    (hchange : side before ≠ side (finRotate n before)) :
    ∃ k : Fin n, 0 < k.1 ∧
      side (finCycle k (finRotate n before)) ≠
        side (finRotate n before) ∧
      ∀ m : Fin n, m < k →
        side (finCycle m (finRotate n before)) =
          side (finRotate n before) := by
  letI : NeZero n := ⟨by omega⟩
  let start : Fin n := finRotate n before
  let p : Fin n → Prop := fun k => side (finCycle k start) ≠ side start
  letI : DecidablePred p := Classical.decPred p
  have hex : ∃ k : Fin n, p k := by
    refine ⟨-1, ?_⟩
    have hback : finCycle (-1 : Fin n) start = before := by
      dsimp [start]
      simp [finCycle_apply, finRotate_apply, add_assoc]
    change side (finCycle (-1 : Fin n) start) ≠ side start
    rw [hback]
    exact hchange
  let k : Fin n := Fin.find p hex
  have hkSpec : p k := Fin.find_spec hex
  have hkpos : 0 < k.1 := by
    by_contra hk
    have hk0 : k = (0 : Fin n) := Fin.ext (by omega)
    subst k
    change side (finCycle (0 : Fin n) start) ≠ side start at hkSpec
    simpa [finCycle_apply] using hkSpec
  refine ⟨k, hkpos, ?_, ?_⟩
  · exact hkSpec
  · intro m hm
    have hnot : ¬ p m := Fin.find_min hex hm
    exact not_ne_iff.mp hnot

/-- A transition determines a positive maximal run on the new side; the
edge at index `before + k` is the last edge of the run and is itself followed
by a side change. -/
theorem exists_cyclic_run_to_change
    {n : ℕ} (hn : 2 ≤ n) (side : Fin n → Bool) (before : Fin n)
    (hchange : side before ≠ side (cyclicSucc before)) :
    ∃ k : Fin n, 0 < k.1 ∧
      (∀ m : Fin n, m < k →
        side (cyclicRunIndex before m) = side (cyclicSucc before)) ∧
      side (before + k) = side (cyclicSucc before) ∧
      side (before + k) ≠ side (cyclicSucc (before + k)) := by
  letI : NeZero n := ⟨by omega⟩
  have hchangeRot : side before ≠ side (finRotate n before) := by
    rw [← cyclicSucc_eq_finRotate]
    exact hchange
  obtain ⟨k, hkpos, hafter, hconst⟩ :=
    exists_first_cyclic_change hn side before hchangeRot
  have hrun : ∀ m : Fin n, m < k →
      side (cyclicRunIndex before m) = side (cyclicSucc before) := by
    intro m hm
    rw [cyclicSucc_eq_finRotate]
    simpa [cyclicRunIndex] using hconst m hm
  let off : Fin n := ⟨k.1 - 1, by omega⟩
  have hoff : off + 1 = k := by
    apply Fin.ext
    simp [off, Fin.add_def]
    rw [Nat.mod_eq_of_lt]
    · omega
    · omega
  have hlastIndex : cyclicRunIndex before off = before + k := by
    rw [cyclicRunIndex, finCycle_apply, finRotate_apply]
    calc
      before + 1 + off = before + (off + 1) := by ac_rfl
      _ = before + k := by rw [hoff]
  have hlastSide : side (before + k) = side (cyclicSucc before) := by
    rw [← hlastIndex]
    exact hrun off (by
      rw [Fin.lt_def]
      dsimp [off]
      omega)
  have hnextIndex :
      finCycle k (finRotate n before) =
        cyclicSucc (before + k) := by
    rw [cyclicSucc_eq_finRotate, finCycle_apply, finRotate_apply,
      finRotate_apply]
    ac_rfl
  have hlastChange :
      side (before + k) ≠ side (cyclicSucc (before + k)) := by
    rw [hlastSide, ← hnextIndex]
    exact hafter.symm
  exact ⟨k, hkpos, hrun, hlastSide, hlastChange⟩

/-- In a nonconstant cyclic Boolean word there is a maximal run on the
false side, bounded by side changes at both ends. -/
theorem exists_false_cyclic_run
    {n : ℕ} (hn : 2 ≤ n) (side : Fin n → Bool)
    (hmix : ∃ i j : Fin n, side i ≠ side j) :
    ∃ before k : Fin n, 0 < k.1 ∧
      side (cyclicSucc before) = false ∧
      (∀ m : Fin n, m < k →
        side (cyclicRunIndex before m) = false) ∧
      side (before + k) = false ∧
      side (cyclicSucc (before + k)) = true := by
  obtain ⟨before, hbeforeRot⟩ :=
    exists_cyclic_change_of_nonconstant side hmix
  have hbefore : side before ≠ side (cyclicSucc before) := by
    rw [cyclicSucc_eq_finRotate]
    exact hbeforeRot
  obtain ⟨k, hkpos, hrun, hlastSide, hlastChange⟩ :=
    exists_cyclic_run_to_change hn side before hbefore
  cases hs : side (cyclicSucc before)
  · refine ⟨before, k, hkpos, hs, ?_, ?_, ?_⟩
    · intro m hm
      simpa [hs] using hrun m hm
    · simpa [hs] using hlastSide
    · have := hlastChange
      rw [hlastSide, hs] at this
      cases hnext : side (cyclicSucc (before + k))
      · exact (this rfl).elim
      · exact hnext
  · have hlastTrue : side (before + k) = true := by
      simpa [hs] using hlastSide
    have hnextFalse : side (cyclicSucc (before + k)) = false := by
      have := hlastChange
      rw [hlastTrue] at this
      cases hnext : side (cyclicSucc (before + k))
      · exact hnext
      · exact (this rfl).elim
    let before₂ : Fin n := before + k
    have hchange₂ :
        side before₂ ≠ side (cyclicSucc before₂) := by
      dsimp [before₂]
      rw [hlastTrue, hnextFalse]
      decide
    obtain ⟨k₂, hk₂pos, hrun₂, hlastSide₂, hlastChange₂⟩ :=
      exists_cyclic_run_to_change hn side before₂ hchange₂
    refine ⟨before₂, k₂, hk₂pos, hnextFalse, ?_, ?_, ?_⟩
    · intro m hm
      simpa [hnextFalse] using hrun₂ m hm
    · simpa [hnextFalse] using hlastSide₂
    · have := hlastChange₂
      rw [hlastSide₂, hnextFalse] at this
      cases hnext : side (cyclicSucc (before₂ + k₂))
      · exact (this rfl).elim
      · exact hnext

/-- A nonconstant cyclic Boolean word has two distinct transition indices. -/
theorem exists_two_cyclic_changes
    {n : ℕ} (hn : 2 ≤ n) (side : Fin n → Bool)
    (hmix : ∃ i j : Fin n, side i ≠ side j) :
    ∃ i j : Fin n, i ≠ j ∧
      side i ≠ side (cyclicSucc i) ∧
      side j ≠ side (cyclicSucc j) := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨i, hiRot⟩ := exists_cyclic_change_of_nonconstant side hmix
  obtain ⟨k, hkpos, hafter, hconst⟩ :=
    exists_first_cyclic_change hn side i hiRot
  let start : Fin n := finRotate n i
  let offLast : Fin n := ⟨k.1 - 1, by omega⟩
  let j : Fin n := finCycle offLast start
  have hoff : offLast + 1 = k := by
    apply Fin.ext
    simp [offLast, Fin.add_def]
    rw [Nat.mod_eq_of_lt]
    · omega
    · omega
  have hjconst : side j = side start := by
    exact hconst offLast (by
      rw [Fin.lt_def]
      dsimp [offLast]
      omega)
  have hsucc : cyclicSucc j = finCycle k start := by
    rw [cyclicSucc_eq_finRotate, finRotate_apply]
    dsimp [j]
    rw [finCycle_apply, finCycle_apply]
    calc
      start + offLast + 1 = start + (offLast + 1) := by ac_rfl
      _ = start + k := by rw [hoff]
  have hj : side j ≠ side (cyclicSucc j) := by
    rw [hjconst, hsucc]
    exact hafter.symm
  have hjform : j = i + k := by
    dsimp [j, start]
    rw [finCycle_apply, finRotate_apply]
    calc
      i + 1 + offLast = i + (offLast + 1) := by ac_rfl
      _ = i + k := by rw [hoff]
  have hij : i ≠ j := by
    intro hij
    have hik : i = i + k := hij.trans hjform
    have hkzero : k = 0 := by
      apply add_left_cancel (a := i)
      simpa using hik
    have hv := congrArg Fin.val hkzero
    simpa using hkpos.ne' hv
  have hi : side i ≠ side (cyclicSucc i) := by
    rw [cyclicSucc_eq_finRotate]
    exact hiRot
  exact ⟨i, j, hij, hi, hj⟩

end StructuralRamsey.Girth

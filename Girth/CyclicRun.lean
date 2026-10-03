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

/-- A proper positive offset after the successor of `before` cannot return
to `before`. -/
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
    change (1 + offset.1) % n = offset.1 + 1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
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
    have hkval : k.1 = 0 := Nat.eq_zero_of_not_pos hk
    have hk0 : k = (0 : Fin n) := Fin.ext hkval
    have hkSpec0 : p (0 : Fin n) := hk0 ▸ hkSpec
    simpa [p, finCycle_apply] using hkSpec0
  refine ⟨k, hkpos, hkSpec, ?_⟩
  intro m hm
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
    simpa only [cyclicSucc_eq_finRotate] using hchange
  obtain ⟨k, hkpos, hafter, hconst⟩ :=
    exists_first_cyclic_change hn side before hchangeRot
  have hrun : ∀ m : Fin n, m < k →
      side (cyclicRunIndex before m) = side (cyclicSucc before) := by
    intro m hm
    simpa only [cyclicRunIndex, cyclicSucc_eq_finRotate] using hconst m hm
  let off : Fin n := ⟨k.1 - 1, by omega⟩
  have hoff : off + 1 = k := by
    apply Fin.ext
    change ((off.1 + 1) % n) = k.1
    rw [Nat.mod_eq_of_lt (by omega)]
    dsimp [off]
    omega
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
    intro heq
    apply hafter
    calc
      side (finCycle k (finRotate n before)) =
          side (cyclicSucc (before + k)) := congrArg side hnextIndex
      _ = side (before + k) := heq.symm
      _ = side (cyclicSucc before) := hlastSide
      _ = side (finRotate n before) :=
        congrArg side (cyclicSucc_eq_finRotate before)
  exact ⟨k, hkpos, hrun, hlastSide, hlastChange⟩

/-- In a nonconstant cyclic Boolean word there is a maximal run on the
false side, bounded by side changes at both ends. -/
theorem exists_false_cyclic_run
    {n : ℕ} (hn : 2 ≤ n) (side : Fin n → Bool)
    (hmix : ∃ i j : Fin n, side i ≠ side j) :
    ∃ before k : Fin n, 0 < k.1 ∧
      side before = true ∧
      side (cyclicSucc before) = false ∧
      (∀ m : Fin n, m < k →
        side (cyclicRunIndex before m) = false) ∧
      side (before + k) = false ∧
      side (cyclicSucc (before + k)) = true := by
  obtain ⟨before, hbeforeRot⟩ :=
    exists_cyclic_change_of_nonconstant side hmix
  have hbefore : side before ≠ side (cyclicSucc before) := by
    simpa only [cyclicSucc_eq_finRotate] using hbeforeRot
  obtain ⟨k, hkpos, hrun, hlastSide, hlastChange⟩ :=
    exists_cyclic_run_to_change hn side before hbefore
  cases hs : side (cyclicSucc before) with
  | false =>
      have hbeforeTrue : side before = true := by
        apply Bool.eq_true_of_not_eq_false
        intro hb
        apply hbefore
        rw [hb, hs]
      have hlastFalse : side (before + k) = false := by
        exact hlastSide.trans hs
      have hnextTrue : side (cyclicSucc (before + k)) = true := by
        apply Bool.eq_true_of_not_eq_false
        intro hnxt
        apply hlastChange
        rw [hlastFalse, hnxt]
      refine ⟨before, k, hkpos, hbeforeTrue, hs, ?_, hlastFalse, hnextTrue⟩
      intro m hm
      exact (hrun m hm).trans hs
  | true =>
      have hbeforeFalse : side before = false := by
        apply Bool.eq_false_of_not_eq_true
        intro hb
        apply hbefore
        rw [hb, hs]
      have hlastTrue : side (before + k) = true := by
        exact hlastSide.trans hs
      have hnextFalse : side (cyclicSucc (before + k)) = false := by
        apply Bool.eq_false_of_not_eq_true
        intro hnxt
        apply hlastChange
        rw [hlastTrue, hnxt]
      let before₂ : Fin n := before + k
      have hsucc₂ : side (cyclicSucc before₂) = false := by
        simpa [before₂] using hnextFalse
      have hchange₂ :
          side before₂ ≠ side (cyclicSucc before₂) := by
        intro hEq
        rw [hlastTrue, hsucc₂] at hEq
        contradiction
      obtain ⟨k₂, hk₂pos, hrun₂, hlastSide₂, hlastChange₂⟩ :=
        exists_cyclic_run_to_change hn side before₂ hchange₂
      have hlastFalse₂ : side (before₂ + k₂) = false :=
        hlastSide₂.trans hsucc₂
      have hnextTrue₂ : side (cyclicSucc (before₂ + k₂)) = true := by
        apply Bool.eq_true_of_not_eq_false
        intro hnxt
        apply hlastChange₂
        rw [hlastFalse₂, hnxt]
      refine ⟨before₂, k₂, hk₂pos, hlastTrue, hsucc₂, ?_,
        hlastFalse₂, hnextTrue₂⟩
      intro m hm
      exact (hrun₂ m hm).trans hsucc₂

end StructuralRamsey.Girth

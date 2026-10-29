import Girth.CyclicRun

/-!
# Cyclic switching at a forest leaf

The forest-to-supreme argument uses a binary word recording whether each
occurrence belongs to a fixed leaf.  Acceptability confines the switches to
two consecutive connector positions.  The occurrence between those positions
is therefore the only occurrence on one side of the leaf cut.

The statements here concern the actual cyclic word, including its wraparound.
They allow arbitrary repeated owners.  No segmentation or singleton-run
hypothesis is assumed.
-/

namespace StructuralRamsey.Girth

universe u

/-- Every position other than `before` has a proper offset in the cyclic run
starting just after `before`. -/
theorem cyclicRunIndex_exists_of_ne_before
    {n : ℕ} (hn : 2 ≤ n) (before i : Fin n) (hi : i ≠ before) :
    ∃ offset : Fin n, offset.val + 1 < n ∧
      cyclicRunIndex before offset = i := by
  letI : NeZero n := ⟨by omega⟩
  let offset : Fin n := i - (before + 1)
  have hAt : cyclicRunIndex before offset = i := by
    simp only [cyclicRunIndex, finCycle_apply, finRotate_apply, offset]
    abel
  refine ⟨offset, ?_, hAt⟩
  by_contra hNot
  have hTop : offset.val + 1 = n := by
    have := offset.isLt
    omega
  have hZero : offset + 1 = (0 : Fin n) := by
    apply Fin.ext
    change (offset.val + (1 % n)) % n = 0
    rw [Nat.mod_eq_of_lt (show 1 < n by omega), hTop, Nat.mod_self]
  apply hi
  calc
    i = cyclicRunIndex before offset := hAt.symm
    _ = before + 1 + offset := by
      simp only [cyclicRunIndex, finCycle_apply, finRotate_apply]
    _ = before + (offset + 1) := by ac_rfl
    _ = before := by rw [hZero, add_zero]

/-- Deleting one occurrence from a cyclic word leaves a connected run.
Equality along every surviving successor link forces all surviving owners
to agree. -/
theorem cyclicOwner_eq_off_singleton
    {n : ℕ} {Owner : Type u} (hn : 2 ≤ n)
    (owner : Fin n → Owner) (k : Fin n)
    (hStep : ∀ j : Fin n, j ≠ k → cyclicSucc j ≠ k →
      owner j = owner (cyclicSucc j))
    (i : Fin n) (hi : i ≠ k) :
    owner i = owner (cyclicSucc k) := by
  letI : NeZero n := ⟨by omega⟩
  have hRun : ∀ (t : ℕ) (ht : t < n), t + 1 < n →
      owner (cyclicRunIndex k ⟨t, ht⟩) = owner (cyclicSucc k) := by
    intro t
    induction t with
    | zero =>
        intro ht _
        simp [cyclicRunIndex, finCycle_apply, cyclicSucc_eq_finRotate]
    | succ t ih =>
        intro ht hProper
        have htPrev : t < n := by omega
        let a : Fin n := ⟨t, htPrev⟩
        let b : Fin n := ⟨t + 1, ht⟩
        have hAdd : a + 1 = b := by
          apply Fin.ext
          change (t + (1 % n)) % n = t + 1
          rw [Nat.mod_eq_of_lt (show 1 < n by omega),
            Nat.mod_eq_of_lt ht]
        have hNext : cyclicSucc (cyclicRunIndex k a) =
            cyclicRunIndex k b := by
          simp only [cyclicSucc_eq_finRotate, cyclicRunIndex,
            finCycle_apply, finRotate_apply]
          rw [add_assoc, hAdd]
        have ha : cyclicRunIndex k a ≠ k :=
          cyclicRunIndex_ne_before k a (by dsimp [a]; omega)
        have hb : cyclicSucc (cyclicRunIndex k a) ≠ k := by
          rw [hNext]
          exact cyclicRunIndex_ne_before k b hProper
        calc
          owner (cyclicRunIndex k b) =
              owner (cyclicSucc (cyclicRunIndex k a)) :=
            congrArg owner hNext.symm
          _ = owner (cyclicRunIndex k a) := (hStep _ ha hb).symm
          _ = owner (cyclicSucc k) := ih htPrev (by omega)
  obtain ⟨offset, hProper, hAt⟩ :=
    cyclicRunIndex_exists_of_ne_before hn k i hi
  rw [← hAt]
  exact hRun offset.val offset.isLt hProper

/-- If all changes occur at two consecutive connector positions `p` and
`succ p`, every occurrence other than their shared occurrence has the same
owner as `p`. -/
theorem cyclicOwner_constant_off_consecutive_cuts
    {n : ℕ} {Owner : Type u} (hn : 2 ≤ n)
    (owner : Fin n → Owner) (p : Fin n)
    (hCuts : ∀ j : Fin n, owner j ≠ owner (cyclicSucc j) →
      j = p ∨ j = cyclicSucc p) :
    ∀ i : Fin n, i ≠ cyclicSucc p → owner i = owner p := by
  have hStep : ∀ j : Fin n, j ≠ cyclicSucc p →
      cyclicSucc j ≠ cyclicSucc p →
      owner j = owner (cyclicSucc j) := by
    intro j hj hsj
    by_contra hChange
    rcases hCuts j hChange with hp | hp
    · exact hsj (congrArg cyclicSucc hp)
    · exact hj hp
  have hp : p ≠ cyclicSucc p := by
    intro h
    have hv := congrArg Fin.val h
    change p.val = (p.val + 1) % n at hv
    by_cases hlt : p.val + 1 < n
    · rw [Nat.mod_eq_of_lt hlt] at hv
      omega
    · have heq : p.val + 1 = n := by have := p.isLt; omega
      rw [heq, Nat.mod_self] at hv
      omega
  intro i hi
  exact (cyclicOwner_eq_off_singleton hn owner (cyclicSucc p) hStep i hi).trans
    (cyclicOwner_eq_off_singleton hn owner (cyclicSucc p) hStep p hp).symm

/-- A nonconstant binary word whose switches are confined to two consecutive
connector positions has a singleton side.  The index is the actual occurrence
between those positions, not an independently assumed run representative. -/
theorem cyclicBool_singleton_side_of_consecutive_cuts
    {n : ℕ} (hn : 2 ≤ n) (side : Fin n → Bool) (p : Fin n)
    (hCuts : ∀ j : Fin n, side j ≠ side (cyclicSucc j) →
      j = p ∨ j = cyclicSucc p)
    (hMixed : ∃ i j : Fin n, side i ≠ side j) :
    ∀ i : Fin n, side i = side (cyclicSucc p) ↔ i = cyclicSucc p := by
  have hOff := cyclicOwner_constant_off_consecutive_cuts hn side p hCuts
  have hDifferent : side (cyclicSucc p) ≠ side p := by
    intro hEq
    have hConst : ∀ i : Fin n, side i = side p := by
      intro i
      by_cases hi : i = cyclicSucc p
      · simpa [hi] using hEq
      · exact hOff i hi
    obtain ⟨i, j, hij⟩ := hMixed
    exact hij ((hConst i).trans (hConst j).symm)
  intro i
  constructor
  · intro hEq
    by_contra hi
    exact hDifferent (hEq.symm.trans (hOff i hi))
  · rintro rfl
    rfl

/-- A genuinely mixed cyclic binary word crosses between the two sides at
least twice.  The two switches are distinct even when the run wraps past
the last numerical index. -/
theorem cyclicBool_exists_two_distinct_switches
    {n : ℕ} (hn : 2 ≤ n) (side : Fin n → Bool)
    (hMixed : ∃ i j : Fin n, side i ≠ side j) :
    ∃ p q : Fin n, p ≠ q ∧
      side p ≠ side (cyclicSucc p) ∧
      side q ≠ side (cyclicSucc q) := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨p, hpRot⟩ := exists_cyclic_change_of_nonconstant side hMixed
  have hp : side p ≠ side (cyclicSucc p) := by
    simpa only [cyclicSucc_eq_finRotate] using hpRot
  obtain ⟨k, hkPos, _, _, hLast⟩ :=
    exists_cyclic_run_to_change hn side p hp
  refine ⟨p, p + k, ?_, hp, hLast⟩
  intro hEq
  have hkZero : k = (0 : Fin n) := by
    apply add_left_cancel (a := p)
    simpa using hEq.symm
  have hv := congrArg Fin.val hkZero
  simp only [Fin.val_zero] at hv
  omega

/-- Existential version used in a leaf-versus-complement forest split. -/
theorem cyclicBool_has_singleton_side_of_consecutive_cuts
    {n : ℕ} (hn : 2 ≤ n) (side : Fin n → Bool)
    (hMixed : ∃ i j : Fin n, side i ≠ side j)
    (hCuts : ∃ p : Fin n, ∀ j : Fin n,
      side j ≠ side (cyclicSucc j) → j = p ∨ j = cyclicSucc p) :
    ∃ k : Fin n, (∀ i : Fin n, side i = true ↔ i = k) ∨
      (∀ i : Fin n, side i = false ↔ i = k) := by
  obtain ⟨p, hp⟩ := hCuts
  have hSingleton :=
    cyclicBool_singleton_side_of_consecutive_cuts hn side p hp hMixed
  refine ⟨cyclicSucc p, ?_⟩
  cases hs : side (cyclicSucc p) with
  | false =>
      right
      simpa only [hs] using hSingleton
  | true =>
      left
      simpa only [hs] using hSingleton

end StructuralRamsey.Girth

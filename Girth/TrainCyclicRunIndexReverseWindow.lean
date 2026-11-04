import Girth.TrainCyclicRunIndexAllPositions
import Mathlib.Tactic

/-!
# Path A: converse fibre constraints for the total cyclic owner-run index

The forward interval lemmas locate a source occurrence inside its
canonical run. The one-pass physical lift also needs the converse:
knowing its run index must bound its position between the two cuts
of that run.

For an index j > 0, the occurrence is strictly after the preceding
linear cut and at or before cut j. For run zero, the occurrence is in
the head or tail of the cyclic wrap interval. These statements are
purely combinatorial and do not identify geometric owner values
of nonadjacent runs.

No one-pass source plan or supreme transfer is claimed.
-/

namespace StructuralRamsey.Girth
universe v
variable {Owner : Type v} {n : ℕ}

/-- Every source occurrence assigned to a NONZERO run has a genuine
right-hand cut. If the right-cut index set were empty, the total run
index would by definition be zero. -/
theorem cyclicOwnerRunIndex_nonzero_right
    (owner : Fin n → Owner)
    (hk : 0 < cyclicOwnerChanges owner)
    (t : Fin n) (j : Fin (cyclicOwnerChanges owner))
    (hj : cyclicOwnerRunIndex owner hk t = j)
    (hjpos : 0 < j.val) :
    t ≤ cyclicOwnerCutIndex owner j := by
  classical
  by_cases he : (cyclicOwnerRightCutIndices owner t).Nonempty
  · have hh := cyclicOwnerRunIndex_right_bound owner hk t he
    rw [hj] at hh
    exact hh
  · have h0 : cyclicOwnerRunIndex owner hk t =
        (⟨0, hk⟩ : Fin (cyclicOwnerChanges owner)) := by
      simp [cyclicOwnerRunIndex, he]
    have heq : j = (⟨0, hk⟩ :
        Fin (cyclicOwnerChanges owner)) := hj.symm.trans h0
    have hv := congrArg Fin.val heq
    have hzero : j.val = 0 := hv
    omega

/-- If run j is nonzero, the corresponding occurrence is strictly
AFTER the cut ending run j-1. The immediate predecessor cut in the
LINEAR order is expressed by index j.val-1. -/
theorem cyclicOwnerRunIndex_nonzero_left
    (owner : Fin n → Owner)
    (hk : 0 < cyclicOwnerChanges owner)
    (t : Fin n) (j : Fin (cyclicOwnerChanges owner))
    (hj : cyclicOwnerRunIndex owner hk t = j)
    (hjpos : 0 < j.val) :
    cyclicOwnerCutIndex owner
      (⟨j.val - 1, by omega⟩ :
        Fin (cyclicOwnerChanges owner)) < t := by
  classical
  let prev : Fin (cyclicOwnerChanges owner) :=
    ⟨j.val - 1, by omega⟩
  by_contra hNot
  have hRight : t ≤ cyclicOwnerCutIndex owner prev :=
    le_of_not_gt hNot
  have hLe : cyclicOwnerRunIndex owner hk t ≤ prev :=
    cyclicOwnerRunIndex_le_of_right owner hk t prev hRight
  rw [hj] at hLe
  have hv : j.val ≤ prev.val := hLe
  dsimp [prev] at hv
  omega

/-- The complete CONVERSE membership constraint for every nonzero
canonical run. This rules out falsely assigning a third original
occurrence to a one- or two-step owner run. -/
theorem cyclicOwnerRunIndex_nonzero_window
    (owner : Fin n → Owner)
    (hk : 0 < cyclicOwnerChanges owner)
    (t : Fin n) (j : Fin (cyclicOwnerChanges owner))
    (hj : cyclicOwnerRunIndex owner hk t = j)
    (hjpos : 0 < j.val) :
    cyclicOwnerCutIndex owner
      (⟨j.val - 1, by omega⟩ :
        Fin (cyclicOwnerChanges owner)) < t ∧
      t ≤ cyclicOwnerCutIndex owner j :=
  ⟨cyclicOwnerRunIndex_nonzero_left owner hk t j hj hjpos,
    cyclicOwnerRunIndex_nonzero_right owner hk t j hj hjpos⟩

/-- An original occurrence in run zero is either at or before the
FIRST linearly indexed cut or strictly after the LAST one.
Those are the two pieces of the single cyclic wrap interval. -/
theorem cyclicOwnerRunIndex_zero_wrap_window
    (owner : Fin n → Owner)
    (hk : 0 < cyclicOwnerChanges owner)
    (t : Fin n)
    (hj : cyclicOwnerRunIndex owner hk t =
      (⟨0, hk⟩ : Fin (cyclicOwnerChanges owner))) :
    t ≤ cyclicOwnerFirstCut owner hk ∨
      cyclicOwnerLastCut owner hk < t := by
  classical
  by_cases he : (cyclicOwnerRightCutIndices owner t).Nonempty
  · left
    have hh := cyclicOwnerRunIndex_right_bound owner hk t he
    rw [hj] at hh
    change t ≤ cyclicOwnerFirstCut owner hk at hh
    exact hh
  · right
    have hNot : ¬ t ≤ cyclicOwnerLastCut owner hk := by
      intro hh
      have hMem : (⟨cyclicOwnerChanges owner - 1, by omega⟩ :
          Fin (cyclicOwnerChanges owner)) ∈
          cyclicOwnerRightCutIndices owner t :=
        (mem_cyclicOwnerRightCutIndices_iff owner t _).mpr hh
      exact he ⟨_, hMem⟩
    exact lt_of_not_ge hNot

/-- Two source indices strictly between the predecessor and successor
of t in the LINEAR Fin n order must be t or its successor. The
hypotheses are contradictory when this two-step segment wraps. -/
private theorem cyclic_two_step_linear_window
    {n : ℕ} (hn : 3 ≤ n) (t x : Fin n)
    (hLeft : trainCyclicPred t < x)
    (hRight : x ≤ cyclicSucc t) :
    x = t ∨ x = cyclicSucc t := by
  by_cases hZero : t.val = 0
  · have hp : (trainCyclicPred t).val = n - 1 := by
      change (t.val + n - 1) % n = n - 1
      rw [hZero]
      simpa using (Nat.mod_eq_of_lt (show n - 1 < n by omega))
    have hv : n - 1 < x.val := by
      rw [← hp]
      exact hLeft
    have hx := x.isLt
    omega
  · by_cases hLast : t.val + 1 = n
    · have hp : (trainCyclicPred t).val = n - 2 := by
        change (t.val + n - 1) % n = n - 2
        have hNum : t.val + n - 1 = n + (n - 2) := by omega
        rw [hNum, Nat.add_mod]
        simp [Nat.mod_eq_of_lt (show n - 2 < n by omega)]
      have hs : (cyclicSucc t).val = 0 := by
        change (t.val + 1) % n = 0
        rw [hLast, Nat.mod_self]
      have hL : n - 2 < x.val := by
        rw [← hp]
        exact hLeft
      have hR : x.val ≤ 0 := by
        rw [← hs]
        exact hRight
      omega
    · have htPos : 0 < t.val := by omega
      have htBefore : t.val + 1 < n := by
        have := t.isLt
        omega
      have hp : (trainCyclicPred t).val = t.val - 1 := by
        change (t.val + n - 1) % n = t.val - 1
        have hNum : t.val + n - 1 = n + (t.val - 1) := by omega
        rw [hNum, Nat.add_mod]
        simp [Nat.mod_eq_of_lt (show t.val - 1 < n by omega)]
      have hs : (cyclicSucc t).val = t.val + 1 := by
        change (t.val + 1) % n = t.val + 1
        exact Nat.mod_eq_of_lt htBefore
      have hxL : t.val - 1 < x.val := by
        rw [← hp]
        exact hLeft
      have hxR : x.val ≤ t.val + 1 := by
        rw [← hs]
        exact hRight
      have hx : x.val = t.val ∨ x.val = t.val + 1 := by omega
      rcases hx with hAt | hNext
      · exact Or.inl (Fin.ext hAt)
      · exact Or.inr (Fin.ext (hNext.trans hs.symm))

/-- If the two-step boundary interval crosses the LAST/FIRST
source positions, any member of the cyclic head/tail interval is
one of the two original occurrences. -/
private theorem cyclic_two_step_wrap_window
    {n : ℕ} (hn : 3 ≤ n) (t x : Fin n)
    (hWrap : cyclicSucc t < trainCyclicPred t)
    (hWindow : x ≤ cyclicSucc t ∨ trainCyclicPred t < x) :
    x = t ∨ x = cyclicSucc t := by
  by_cases hZero : t.val = 0
  · have hp : (trainCyclicPred t).val = n - 1 := by
      change (t.val + n - 1) % n = n - 1
      rw [hZero]
      simpa using (Nat.mod_eq_of_lt (show n - 1 < n by omega))
    have hs : (cyclicSucc t).val = 1 := by
      change (t.val + 1) % n = 1
      rw [hZero]
      exact Nat.mod_eq_of_lt (by omega)
    rcases hWindow with hHead | hTail
    · have hxLe : x.val ≤ 1 := by
        rw [← hs]
        exact hHead
      have hxCase : x.val = 0 ∨ x.val = 1 := by omega
      rcases hxCase with hAt | hNext
      · exact Or.inl (Fin.ext (hAt.trans hZero.symm))
      · exact Or.inr (Fin.ext (hNext.trans hs.symm))
    · have hxGt : n - 1 < x.val := by
        rw [← hp]
        exact hTail
      have hxBound := x.isLt
      omega
  · by_cases hLast : t.val + 1 = n
    · have hp : (trainCyclicPred t).val = n - 2 := by
        change (t.val + n - 1) % n = n - 2
        have hNum : t.val + n - 1 = n + (n - 2) := by omega
        rw [hNum, Nat.add_mod]
        simp [Nat.mod_eq_of_lt (show n - 2 < n by omega)]
      have hs : (cyclicSucc t).val = 0 := by
        change (t.val + 1) % n = 0
        rw [hLast, Nat.mod_self]
      rcases hWindow with hHead | hTail
      · have hx0 : x.val ≤ 0 := by
          rw [← hs]
          exact hHead
        exact Or.inr (Fin.ext (by omega : x.val = (cyclicSucc t).val))
      · have hxLow : n - 2 < x.val := by
          rw [← hp]
          exact hTail
        have hxUp := x.isLt
        exact Or.inl (Fin.ext (by omega : x.val = t.val))
    · have htPos : 0 < t.val := by omega
      have htBefore : t.val + 1 < n := by
        have := t.isLt
        omega
      have hp : (trainCyclicPred t).val = t.val - 1 := by
        change (t.val + n - 1) % n = t.val - 1
        have hNum : t.val + n - 1 = n + (t.val - 1) := by omega
        rw [hNum, Nat.add_mod]
        simp [Nat.mod_eq_of_lt (show t.val - 1 < n by omega)]
      have hs : (cyclicSucc t).val = t.val + 1 := by
        change (t.val + 1) % n = t.val + 1
        exact Nat.mod_eq_of_lt htBefore
      have hw : t.val + 1 < t.val - 1 := by
        have hh : (cyclicSucc t).val < (trainCyclicPred t).val := hWrap
        rw [hs, hp] at hh
        exact hh
      omega

/-- Exact converse for a TWO-STEP run. If its consecutive canonical
boundary cuts are the predecessor and successor of t, then the
ONLY original source positions assigned to that reduced run are
t and cyclicSucc t, including cyclic wraparound.

No assumption of geometric ownership or physical wagon incidence is
used here; those are provided separately by the checked Path A
two-step long geometry theorem. -/
theorem cyclicOwnerRunIndex_two_step_fibre
    (owner : Fin n → Owner)
    (hn : 3 ≤ n) (hThree : 3 ≤ cyclicOwnerChanges owner)
    (j : Fin (cyclicOwnerChanges owner))
    (t x : Fin n)
    (hPrev : cyclicOwnerCutIndex owner (trainCyclicPred j) =
      trainCyclicPred t)
    (hHere : cyclicOwnerCutIndex owner j = cyclicSucc t)
    (hx : cyclicOwnerRunIndex owner (by omega) x = j) :
    x = t ∨ x = cyclicSucc t := by
  let q := cyclicOwnerChanges owner
  have hq : 0 < q := by omega
  by_cases hjPos : 0 < j.val
  · let i : Fin q := ⟨j.val - 1, by omega⟩
    have hPred : trainCyclicPred j = i := by
      apply Fin.ext
      change (j.val + q - 1) % q = j.val - 1
      have hv : j.val + q - 1 = q + (j.val - 1) := by omega
      rw [hv, Nat.add_mod]
      simp [Nat.mod_eq_of_lt (show j.val - 1 < q by omega)]
    have hWindow :=
      cyclicOwnerRunIndex_nonzero_window owner hq x j hx hjPos
    have hLeft : trainCyclicPred t < x := by
      have hh := hWindow.1
      change cyclicOwnerCutIndex owner i < x at hh
      rw [← hPred, hPrev] at hh
      exact hh
    have hRight : x ≤ cyclicSucc t := by
      have hh := hWindow.2
      rw [hHere] at hh
      exact hh
    exact cyclic_two_step_linear_window hn t x hLeft hRight
  · have hjZero : j.val = 0 := by omega
    have hZero : j = (⟨0, hq⟩ : Fin q) :=
      Fin.ext hjZero
    have hRunZero : cyclicOwnerRunIndex owner hq x =
        (⟨0, hq⟩ : Fin q) := hx.trans hZero
    have hWindow :=
      cyclicOwnerRunIndex_zero_wrap_window owner hq x hRunZero
    have hPredVal : (trainCyclicPred j).val = q - 1 := by
      change (j.val + q - 1) % q = q - 1
      rw [hjZero]
      simpa using (Nat.mod_eq_of_lt (show q - 1 < q by omega))
    have hPrevLast : trainCyclicPred j =
        (⟨q - 1, by omega⟩ : Fin q) :=
      Fin.ext hPredVal
    have hLast : cyclicOwnerLastCut owner hq =
        trainCyclicPred t := by
      change cyclicOwnerCutIndex owner
        (⟨q - 1, by omega⟩ : Fin q) = trainCyclicPred t
      rw [← hPrevLast]
      exact hPrev
    have hFirst : cyclicOwnerFirstCut owner hq =
        cyclicSucc t := by
      change cyclicOwnerCutIndex owner (⟨0, hq⟩ : Fin q) =
        cyclicSucc t
      rw [← hZero]
      exact hHere
    have hJLess : j < trainCyclicPred j := by
      change j.val < (trainCyclicPred j).val
      rw [hjZero, hPredVal]
      omega
    have hCutOrder :
        cyclicSucc t < trainCyclicPred t := by
      have hh := (cyclicOwnerCutIndex owner).strictMono hJLess
      rw [hHere, hPrev] at hh
      exact hh
    have hSourceWindow :
        x ≤ cyclicSucc t ∨ trainCyclicPred t < x := by
      rcases hWindow with hHead | hTail
      · exact Or.inl (by rw [← hFirst]; exact hHead)
      · exact Or.inr (by rw [← hLast]; exact hTail)
    exact cyclic_two_step_wrap_window hn t x hCutOrder hSourceWindow

end StructuralRamsey.Girth

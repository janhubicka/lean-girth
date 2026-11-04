import Girth.TrainActualThreeCutNonadjacentLong
import Mathlib.Tactic

/-!
# Path A: consecutive cut indices across a single uncut position

If both cyclic neighbours of t are owner-cut positions but t itself
is not, those two neighbouring cuts are consecutive in the CANONICAL
cyclic cut enumeration. This holds in all three cases (t=0, t=n-1,
and the interior) and does not assume an order on the owner type.

Thus if at least three owner cuts exist, two consecutive reduced cuts
cannot occur in the *opposite* orientation around one uncut point.
This is the missing finite orientation check for the source-A2
old-wagon obstruction in the selected non-singleton long branch.

No appendix and no claim of actual physical replacement.
-/

namespace StructuralRamsey.Girth

universe v

/-- The two original cut positions separated by exactly one uncut
position t appear consecutively in the canonical CYCLIC reduced list,
including when t is at either end of the linear Fin order. -/
theorem cyclicOwnerCutIndex_pred_of_single_uncut_gap
    {Owner : Type v} {n : ℕ}
    (owner : Fin n → Owner) (hn : 3 ≤ n)
    (t : Fin n)
    (hPrevious : trainCyclicPred t ∈ cyclicOwnerCutPositions owner)
    (hNext : cyclicSucc t ∈ cyclicOwnerCutPositions owner)
    (hUncut : t ∉ cyclicOwnerCutPositions owner) :
    ∃ j : Fin (cyclicOwnerChanges owner),
      cyclicOwnerCutIndex owner j = cyclicSucc t ∧
      cyclicOwnerCutIndex owner (trainCyclicPred j) =
        trainCyclicPred t := by
  classical
  let f := cyclicOwnerCutIndex owner
  let q := cyclicOwnerChanges owner
  obtain ⟨a, ha⟩ :=
    (cyclicOwnerCutIndex_mem_iff owner (trainCyclicPred t)).mp hPrevious
  obtain ⟨b, hb⟩ :=
    (cyclicOwnerCutIndex_mem_iff owner (cyclicSucc t)).mp hNext
  have hA : f a = trainCyclicPred t := ha
  have hB : f b = cyclicSucc t := hb
  have hPrevNeNext : trainCyclicPred t ≠ cyclicSucc t := by
    intro hEq
    have hs := congrArg cyclicSucc hEq
    rw [cyclicSucc_trainCyclicPred_of_two_le
      (by omega : 2 ≤ n) t] at hs
    exact (cyclicSucc_succ_ne_self_of_three_le hn t) hs.symm
  have hab : a ≠ b := by
    intro heq
    apply hPrevNeNext
    calc
      trainCyclicPred t = f a := hA.symm
      _ = f b := congrArg f heq
      _ = cyclicSucc t := hB
  have hq : 2 ≤ q := by
    have hneq : a.val ≠ b.val := by
      intro heq
      exact hab (Fin.ext heq)
    have haBound := a.isLt
    have hbBound := b.isLt
    dsimp [q] at *
    omega
  have hNextIndex : cyclicSucc a = b := by
    by_cases hZero : t.val = 0
    · have hPrevVal : (trainCyclicPred t).val = n - 1 := by
        change (t.val + n - 1) % n = n - 1
        rw [hZero]
        simp only [zero_add]
        exact Nat.mod_eq_of_lt (by omega)
      have hSuccVal : (cyclicSucc t).val = 1 := by
        change (t.val + 1) % n = 1
        rw [hZero]
        exact Nat.mod_eq_of_lt (by omega)
      have haLast : a.val + 1 = q := by
        by_contra hNot
        have hNextBound : a.val + 1 < q := by
          have := a.isLt
          omega
        let later : Fin q := ⟨a.val + 1, hNextBound⟩
        have hALess : a < later := by
          change a.val < a.val + 1
          omega
        have hFLess : (f a).val < (f later).val :=
          f.strictMono hALess
        rw [hA, hPrevVal] at hFLess
        have hUpper := (f later).isLt
        omega
      have hbFirst : b.val = 0 := by
        by_contra hNot
        have hbPos : 0 < b.val := by omega
        let first : Fin q := ⟨0, by omega⟩
        have hLess : first < b := by
          change 0 < b.val
          exact hbPos
        have hFLess : (f first).val < (f b).val :=
          f.strictMono hLess
        rw [hB, hSuccVal] at hFLess
        have hVal : (f first).val = t.val := by omega
        have ht : f first = t := Fin.ext hVal
        exact hUncut
          ((cyclicOwnerCutIndex_mem_iff owner t).mpr ⟨first, ht⟩)
      apply Fin.ext
      change (a.val + 1) % q = b.val
      rw [haLast, Nat.mod_self]
      exact hbFirst.symm
    · by_cases hLast : t.val + 1 = n
      · have hPrevVal : (trainCyclicPred t).val = n - 2 := by
          change (t.val + n - 1) % n = n - 2
          have hNum : t.val + n - 1 = n + (n - 2) := by omega
          rw [hNum, Nat.add_mod]
          simp [Nat.mod_eq_of_lt (show n - 2 < n by omega)]
        have hSuccVal : (cyclicSucc t).val = 0 := by
          change (t.val + 1) % n = 0
          rw [hLast, Nat.mod_self]
        have haLast : a.val + 1 = q := by
          by_contra hNot
          have hNextBound : a.val + 1 < q := by
            have := a.isLt
            omega
          let later : Fin q := ⟨a.val + 1, hNextBound⟩
          have hALess : a < later := by
            change a.val < a.val + 1
            omega
          have hFLess : (f a).val < (f later).val :=
            f.strictMono hALess
          rw [hA, hPrevVal] at hFLess
          have hUpper := (f later).isLt
          have hVal : (f later).val = t.val := by omega
          have ht : f later = t := Fin.ext hVal
          exact hUncut
            ((cyclicOwnerCutIndex_mem_iff owner t).mpr ⟨later, ht⟩)
        have hbFirst : b.val = 0 := by
          by_contra hNot
          have hbPos : 0 < b.val := by omega
          let first : Fin q := ⟨0, by omega⟩
          have hLess : first < b := by
            change 0 < b.val
            exact hbPos
          have hFLess : (f first).val < (f b).val :=
            f.strictMono hLess
          rw [hB, hSuccVal] at hFLess
          omega
        apply Fin.ext
        change (a.val + 1) % q = b.val
        rw [haLast, Nat.mod_self]
        exact hbFirst.symm
      · have htPositive : 0 < t.val := by omega
        have htBeforeLast : t.val + 1 < n := by omega
        have hPrevVal : (trainCyclicPred t).val = t.val - 1 := by
          change (t.val + n - 1) % n = t.val - 1
          have hNum : t.val + n - 1 = n + (t.val - 1) := by omega
          rw [hNum, Nat.add_mod]
          simp [Nat.mod_eq_of_lt (show t.val - 1 < n by omega)]
        have hSuccVal : (cyclicSucc t).val = t.val + 1 := by
          change (t.val + 1) % n = t.val + 1
          exact Nat.mod_eq_of_lt htBeforeLast
        have hAB : a < b := by
          by_contra hNot
          have hBA : b ≤ a := le_of_not_gt hNot
          have hMon : (f b).val ≤ (f a).val :=
            f.monotone hBA
          rw [hA, hB, hPrevVal, hSuccVal] at hMon
          omega
        have hConsecutive : b.val = a.val + 1 := by
          by_contra hNot
          have hGap : a.val + 1 < b.val := by
            have habVal : a.val < b.val := hAB
            omega
          let middle : Fin q := ⟨a.val + 1, by
            have := b.isLt
            omega⟩
          have hLessLeft : a < middle := by
            change a.val < a.val + 1
            omega
          have hLessRight : middle < b := by
            change a.val + 1 < b.val
            exact hGap
          have hFLess : (f a).val < (f middle).val :=
            f.strictMono hLessLeft
          have hFMore : (f middle).val < (f b).val :=
            f.strictMono hLessRight
          rw [hA, hPrevVal] at hFLess
          rw [hB, hSuccVal] at hFMore
          have hVal : (f middle).val = t.val := by omega
          have ht : f middle = t := Fin.ext hVal
          exact hUncut
            ((cyclicOwnerCutIndex_mem_iff owner t).mpr ⟨middle, ht⟩)
        apply Fin.ext
        change (a.val + 1) % q = b.val
        rw [Nat.mod_eq_of_lt (show a.val + 1 < q by
          have := b.isLt
          omega)]
        exact hConsecutive.symm
  have hPred : trainCyclicPred b = a := by
    rw [← hNextIndex]
    exact trainCyclicPred_cyclicSucc_of_two_le hq a
  exact ⟨b, hB, by rw [hPred]; exact hA⟩

/-- A source cut with at least three canonical cuts cannot be both
preceded by the cut at succ t and followed by the cut at pred t when
t itself is not a cut. This excludes the wrong A2 orientation. -/
theorem cyclicOwnerCutIndex_no_reverse_single_uncut_gap_of_three_cuts
    {Owner : Type v} {n : ℕ}
    (owner : Fin n → Owner)
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (cut : Fin (cyclicOwnerChanges owner))
    (t : Fin n)
    (hA : cyclicOwnerCutIndex owner (trainCyclicPred cut) = cyclicSucc t)
    (hB : cyclicOwnerCutIndex owner cut = trainCyclicPred t)
    (hUncut : t ∉ cyclicOwnerCutPositions owner) :
    False := by
  classical
  have hCard : (cyclicOwnerCutPositions owner).card ≤ n := by
    calc
      (cyclicOwnerCutPositions owner).card ≤
        (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hn : 3 ≤ n := by
    rw [cyclicOwnerCutPositions_card owner] at hCard
    omega
  have hPrevCut : trainCyclicPred t ∈ cyclicOwnerCutPositions owner :=
    (cyclicOwnerCutIndex_mem_iff owner (trainCyclicPred t)).mpr
      ⟨cut, hB⟩
  have hNextCut : cyclicSucc t ∈ cyclicOwnerCutPositions owner :=
    (cyclicOwnerCutIndex_mem_iff owner (cyclicSucc t)).mpr
      ⟨trainCyclicPred cut, hA⟩
  obtain ⟨j, hj, hjPred⟩ :=
    cyclicOwnerCutIndex_pred_of_single_uncut_gap
      owner hn t hPrevCut hNextCut hUncut
  have hjEq : j = trainCyclicPred cut := by
    apply (cyclicOwnerCutIndex owner).injective
    exact hj.trans hA.symm
  subst j
  have hDouble : trainCyclicPred (trainCyclicPred cut) = cut := by
    apply (cyclicOwnerCutIndex owner).injective
    exact hjPred.trans hB.symm
  exact (trainCyclicPred_pred_ne_self_of_three_le hThree cut) hDouble

/-- The two A2 orientations of an existing wagon are not symmetric
for a chosen pair of consecutive REDUCED cuts: with >=3 cuts and the
wagon at an uncut source position, only the forward two-step
vertex–wagon–vertex orientation is possible. -/
theorem cyclicOwnerCutIndex_old_uncut_straddle_forward_of_three_cuts
    {Owner : Type v} {n : ℕ}
    (owner : Fin n → Owner)
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (cut : Fin (cyclicOwnerChanges owner))
    (t : Fin n)
    (hUncut : t ∉ cyclicOwnerCutPositions owner)
    (hStraddle :
      (cyclicOwnerCutIndex owner (trainCyclicPred cut) =
          trainCyclicPred t ∧
        cyclicOwnerCutIndex owner cut = cyclicSucc t) ∨
      (cyclicOwnerCutIndex owner (trainCyclicPred cut) =
          cyclicSucc t ∧
        cyclicOwnerCutIndex owner cut = trainCyclicPred t)) :
    cyclicOwnerCutIndex owner (trainCyclicPred cut) = trainCyclicPred t ∧
      cyclicOwnerCutIndex owner cut = cyclicSucc t := by
  rcases hStraddle with hGood | hBad
  · exact hGood
  · exact False.elim
      (cyclicOwnerCutIndex_no_reverse_single_uncut_gap_of_three_cuts
        owner hThree cut t hBad.1 hBad.2 hUncut)

end StructuralRamsey.Girth

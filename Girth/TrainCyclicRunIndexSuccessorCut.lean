import Girth.TrainCyclicRunIndexAllPositions
import Mathlib.Tactic

/-!
# Path A: the original successor of a cut starts the NEXT owner run

The total run-index map assigns each original cut position to its own
reduced index. Its original CYCLIC SUCCESSOR, however, starts the next
maximal run. This theorem identifies its run index with `cyclicSucc j`,
including both the ordinary and the last-to-first cyclic wrap cases.

This is an essential exact-index relation when lifting the SAME
globally selected reduced plan to all original occurrences. It does
not construct the lifted plan. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- After indexed original owner cut j, the next original occurrence
belongs to indexed owner run (cyclicSucc j). Even if j is the last
linearly indexed cut, the index cycles to zero; no owner-name
injectivity across nonadjacent runs is required. -/
theorem cyclicOwnerRunIndex_succ_cut
    (owner : Fin n → Owner)
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (j : Fin (cyclicOwnerChanges owner)) :
    cyclicOwnerRunIndex owner (by omega)
      (cyclicSucc (cyclicOwnerCutIndex owner j)) = cyclicSucc j := by
  classical
  let q := cyclicOwnerChanges owner
  let c := cyclicOwnerCutIndex owner
  let pos := cyclicSucc (c j)
  have hq : 0 < q := by omega
  have hn : 0 < n := by
    have := (c j).isLt
    omega
  by_cases hNext : j.val + 1 < q
  · have hNextIndex :
        cyclicSucc j = (⟨j.val + 1, hNext⟩ : Fin q) := by
      apply Fin.ext
      change (j.val + 1) % q = j.val + 1
      exact Nat.mod_eq_of_lt hNext
    have hIndexLess : j < cyclicSucc j := by
      rw [hNextIndex]
      change j.val < j.val + 1
      omega
    have hSourceLess : c j < c (cyclicSucc j) :=
      c.strictMono hIndexLess
    have hSourceNotLast : (c j).val + 1 < n := by
      have := (c (cyclicSucc j)).isLt
      have hVal : (c j).val < (c (cyclicSucc j)).val := hSourceLess
      omega
    have hPosVal : pos.val = (c j).val + 1 := by
      change ((c j).val + 1) % n = (c j).val + 1
      exact Nat.mod_eq_of_lt hSourceNotLast
    have hPosRight : pos ≤ c (cyclicSucc j) := by
      change pos.val ≤ (c (cyclicSucc j)).val
      rw [hPosVal]
      have hVal : (c j).val < (c (cyclicSucc j)).val := hSourceLess
      omega
    have hRunLe :
        cyclicOwnerRunIndex owner (by omega : 0 < q) pos ≤
          cyclicSucc j :=
      cyclicOwnerRunIndex_le_of_right owner (by omega : 0 < q)
        pos (cyclicSucc j) hPosRight
    have hEligible :
        (cyclicOwnerRightCutIndices owner pos).Nonempty :=
      ⟨cyclicSucc j,
        (mem_cyclicOwnerRightCutIndices_iff owner pos _).mpr hPosRight⟩
    have hRunRight :
        pos ≤ c (cyclicOwnerRunIndex owner (by omega : 0 < q) pos) :=
      cyclicOwnerRunIndex_right_bound owner (by omega : 0 < q)
        pos hEligible
    have hRunAfter : j <
        cyclicOwnerRunIndex owner (by omega : 0 < q) pos := by
      by_contra hNo
      have hRunBefore :
          cyclicOwnerRunIndex owner (by omega : 0 < q) pos ≤ j :=
        le_of_not_gt hNo
      have hSrcBefore :
          c (cyclicOwnerRunIndex owner (by omega : 0 < q) pos) ≤ c j :=
        c.monotone hRunBefore
      have hPosGreater : c j < pos := by
        change (c j).val < pos.val
        rw [hPosVal]
        omega
      exact (not_le_of_gt hPosGreater) (hRunRight.trans hSrcBefore)
    apply Fin.ext
    have hvLe : (cyclicOwnerRunIndex owner (by omega : 0 < q) pos).val ≤
        j.val + 1 := by
      rw [hNextIndex] at hRunLe
      exact hRunLe
    have hvGt : j.val <
        (cyclicOwnerRunIndex owner (by omega : 0 < q) pos).val :=
      hRunAfter
    rw [hNextIndex]
    change (cyclicOwnerRunIndex owner (by omega : 0 < q) pos).val =
      j.val + 1
    omega
  · have hLast : j.val + 1 = q := by
      have := j.isLt
      omega
    have hNextIndex : cyclicSucc j = (⟨0, hq⟩ : Fin q) := by
      apply Fin.ext
      change (j.val + 1) % q = 0
      rw [hLast]
      exact Nat.mod_self q
    have hMax : ∀ k : Fin q, k ≤ j := by
      intro k
      change k.val ≤ j.val
      have := k.isLt
      omega
    by_cases hWrap : (c j).val + 1 = n
    · have hPosZero : pos = (⟨0, hn⟩ : Fin n) := by
        apply Fin.ext
        change ((c j).val + 1) % n = 0
        rw [hWrap]
        exact Nat.mod_self n
      have hRight : pos ≤ c (⟨0, hq⟩ : Fin q) := by
        rw [hPosZero]
        change 0 ≤ (c ⟨0, hq⟩).val
        omega
      have hLe :
          cyclicOwnerRunIndex owner (by omega : 0 < q) pos ≤
            (⟨0, hq⟩ : Fin q) :=
        cyclicOwnerRunIndex_le_of_right owner (by omega : 0 < q)
          pos ⟨0, hq⟩ hRight
      have hEq :
          cyclicOwnerRunIndex owner (by omega : 0 < q) pos =
            (⟨0, hq⟩ : Fin q) := by
        apply Fin.ext
        change (cyclicOwnerRunIndex owner (by omega : 0 < q) pos).val = 0
        have hVal :
            (cyclicOwnerRunIndex owner (by omega : 0 < q) pos).val ≤ 0 :=
          hLe
        omega
      exact hEq.trans hNextIndex.symm
    · have hInside : (c j).val + 1 < n := by
        have := (c j).isLt
        omega
      have hPosVal : pos.val = (c j).val + 1 := by
        change ((c j).val + 1) % n = (c j).val + 1
        exact Nat.mod_eq_of_lt hInside
      have hNoRight :
          ¬ (cyclicOwnerRightCutIndices owner pos).Nonempty := by
        rintro ⟨k, hk⟩
        have hRight : pos ≤ c k :=
          (mem_cyclicOwnerRightCutIndices_iff owner pos k).mp hk
        have hMaxSource : c k ≤ c j :=
          c.monotone (hMax k)
        have hPosGreater : c j < pos := by
          change (c j).val < pos.val
          rw [hPosVal]
          omega
        exact (not_le_of_gt hPosGreater) (hRight.trans hMaxSource)
      have hEq :
          cyclicOwnerRunIndex owner (by omega : 0 < q) pos =
            (⟨0, hq⟩ : Fin q) := by
        simp [cyclicOwnerRunIndex, hNoRight]
      exact hEq.trans hNextIndex.symm

end StructuralRamsey.Girth

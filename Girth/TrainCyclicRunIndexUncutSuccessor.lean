import Girth.TrainCyclicRunIndexAllPositions
import Mathlib.Tactic

/-!
# Path A: an uncut original boundary stays in the same owner run

The canonical right-cut run index is constant across every ORIGINAL
connector where the owner does not change. This covers both ordinary
successors and the wrap n-1 -> 0; at the wrap neither side has an
eligible cut to its linear right, and the first run is chosen.

This literal run-index property is required for source plan assembly:
a chosen reduced replacement belongs to one entire maximal run, not
to an arbitrary choice of different source positions.

It is independent of selected pictures and the appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- When the original owner does not change across a cyclic successor,
both source occurrences belong to the SAME canonically indexed owner
run. No assumption that owner values are globally distinct is needed;
only the actual local no-cut condition matters. -/
theorem cyclicOwnerRunIndex_succ_of_uncut
    (owner : Fin n → Owner)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (t : Fin n)
    (hUncut : owner t = owner (cyclicSucc t)) :
    cyclicOwnerRunIndex owner hCuts (cyclicSucc t) =
      cyclicOwnerRunIndex owner hCuts t := by
  classical
  by_cases hWrap : t.val + 1 = n
  · have hSuccVal : (cyclicSucc t).val = 0 := by
      change (t.val + 1) % n = 0
      rw [hWrap]
      exact Nat.mod_self n
    have hNoEligible : ¬ (cyclicOwnerRightCutIndices owner t).Nonempty := by
      rintro ⟨j, hMem⟩
      have hRight : t ≤ cyclicOwnerCutIndex owner j :=
        (mem_cyclicOwnerRightCutIndices_iff owner t j).mp hMem
      have hCutHere : cyclicOwnerCutIndex owner j = t := by
        apply Fin.ext
        have hBound := (cyclicOwnerCutIndex owner j).isLt
        have hLe : t.val ≤ (cyclicOwnerCutIndex owner j).val := hRight
        omega
      have hActualChange := cyclicOwnerCutIndex_is_change owner j
      rw [hCutHere] at hActualChange
      exact hActualChange hUncut
    have hRunT : cyclicOwnerRunIndex owner hCuts t =
        (⟨0, hCuts⟩ : Fin (cyclicOwnerChanges owner)) := by
      simp [cyclicOwnerRunIndex, hNoEligible]
    have hFirstLe :
        cyclicOwnerRunIndex owner hCuts (cyclicSucc t) ≤
          (⟨0, hCuts⟩ : Fin (cyclicOwnerChanges owner)) := by
      apply cyclicOwnerRunIndex_le_of_right owner hCuts
        (cyclicSucc t) ⟨0, hCuts⟩
      change (cyclicSucc t).val ≤
        (cyclicOwnerCutIndex owner ⟨0, hCuts⟩).val
      rw [hSuccVal]
      omega
    have hRunSucc : cyclicOwnerRunIndex owner hCuts (cyclicSucc t) =
        (⟨0, hCuts⟩ : Fin (cyclicOwnerChanges owner)) := by
      apply Fin.ext
      change (cyclicOwnerRunIndex owner hCuts (cyclicSucc t)).val = 0
      have hv : (cyclicOwnerRunIndex owner hCuts (cyclicSucc t)).val ≤ 0 := by
        simpa only [Fin.le_def, Fin.val_mk] using hFirstLe
      omega
    exact hRunSucc.trans hRunT.symm
  · have hBefore : t.val + 1 < n := by
      have ht := t.isLt
      omega
    have hSuccVal : (cyclicSucc t).val = t.val + 1 := by
      change (t.val + 1) % n = t.val + 1
      exact Nat.mod_eq_of_lt hBefore
    have hRightSets :
        cyclicOwnerRightCutIndices owner t =
          cyclicOwnerRightCutIndices owner (cyclicSucc t) := by
      ext j
      rw [mem_cyclicOwnerRightCutIndices_iff,
        mem_cyclicOwnerRightCutIndices_iff]
      constructor
      · intro hRight
        by_contra hNotRight
        have hCutVal : (cyclicOwnerCutIndex owner j).val = t.val := by
          have hLe : t.val ≤ (cyclicOwnerCutIndex owner j).val := hRight
          have hNot : ¬ (cyclicSucc t).val ≤
              (cyclicOwnerCutIndex owner j).val := hNotRight
          rw [hSuccVal] at hNot
          omega
        have hCutHere : cyclicOwnerCutIndex owner j = t := Fin.ext hCutVal
        have hActualChange := cyclicOwnerCutIndex_is_change owner j
        rw [hCutHere] at hActualChange
        exact hActualChange hUncut
      · intro hRight
        have hNext : t ≤ cyclicSucc t := by
          change t.val ≤ (cyclicSucc t).val
          rw [hSuccVal]
          omega
        exact le_trans hNext hRight
    unfold cyclicOwnerRunIndex
    simp only [hRightSets]

end StructuralRamsey.Girth

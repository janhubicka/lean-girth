import Girth.TrainCyclicRunIndexAllPositions
import Mathlib.Tactic

/-!
# Path A: exact run membership on indexed cut intervals and wrap

The total run index is the least indexed cut at or after each original
position. Its geometric fibres are the ordinary half-open intervals
between consecutive canonical cuts and the unique cyclic wrap interval.

We prove the constructive FORWARD direction used to assemble the
original physical replacement: any original position strictly after
indexed cut i and at or before its next indexed cut belongs to run i+1.
The head and tail pieces of the wrap interval belong to run zero.

The converse fibre identities, original physical pieces and global
supreme conclusion are separate. Circulation only, no appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- An original position between two successive LINEARLY indexed
owner cuts is assigned to the run ending at the latter cut.
No owner-name injectivity or original label provenance is assumed. -/
theorem cyclicOwnerRunIndex_between_consecutive_cuts
    (owner : Fin n → Owner)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (i : Fin (cyclicOwnerChanges owner))
    (hi : i.val + 1 < cyclicOwnerChanges owner)
    (t : Fin n)
    (hAfter : cyclicOwnerCutIndex owner i < t)
    (hBefore : t ≤ cyclicOwnerCutIndex owner
      (⟨i.val + 1, hi⟩ : Fin (cyclicOwnerChanges owner))) :
    cyclicOwnerRunIndex owner hCuts t =
      (⟨i.val + 1, hi⟩ : Fin (cyclicOwnerChanges owner)) := by
  classical
  let j : Fin (cyclicOwnerChanges owner) := ⟨i.val + 1, hi⟩
  have hRunLe : cyclicOwnerRunIndex owner hCuts t ≤ j :=
    cyclicOwnerRunIndex_le_of_right owner hCuts t j hBefore
  have hEligible : (cyclicOwnerRightCutIndices owner t).Nonempty :=
    ⟨j, (mem_cyclicOwnerRightCutIndices_iff owner t j).mpr hBefore⟩
  have hRunRight : t ≤ cyclicOwnerCutIndex owner
      (cyclicOwnerRunIndex owner hCuts t) :=
    cyclicOwnerRunIndex_right_bound owner hCuts t hEligible
  have hRunAfter : i < cyclicOwnerRunIndex owner hCuts t := by
    by_contra hNot
    have hLe : cyclicOwnerRunIndex owner hCuts t ≤ i :=
      le_of_not_gt hNot
    have hSourceLe := (cyclicOwnerCutIndex owner).monotone hLe
    exact (not_le_of_gt hAfter) (hRunRight.trans hSourceLe)
  apply Fin.ext
  change (cyclicOwnerRunIndex owner hCuts t).val = i.val + 1
  have hvLe : (cyclicOwnerRunIndex owner hCuts t).val ≤ i.val + 1 :=
    hRunLe
  have hvGt : i.val < (cyclicOwnerRunIndex owner hCuts t).val :=
    hRunAfter
  omega

/-- An original position at or before the FIRST indexed physical cut
lies in run zero. This includes source position zero and the cut
position itself; the pre-cut portion is the cyclic wrap run's head. -/
theorem cyclicOwnerRunIndex_before_first_cut
    (owner : Fin n → Owner)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (t : Fin n)
    (hBefore : t ≤ cyclicOwnerCutIndex owner
      (⟨0, hCuts⟩ : Fin (cyclicOwnerChanges owner))) :
    cyclicOwnerRunIndex owner hCuts t =
      (⟨0, hCuts⟩ : Fin (cyclicOwnerChanges owner)) := by
  have hLe : cyclicOwnerRunIndex owner hCuts t ≤
      (⟨0, hCuts⟩ : Fin (cyclicOwnerChanges owner)) :=
    cyclicOwnerRunIndex_le_of_right owner hCuts t ⟨0, hCuts⟩ hBefore
  apply Fin.ext
  change (cyclicOwnerRunIndex owner hCuts t).val = 0
  have hv : (cyclicOwnerRunIndex owner hCuts t).val ≤ 0 := hLe
  omega

/-- An original position AFTER the last linearly indexed cut
has no eligible right cut; hence it belongs to the same cyclic
wrap run zero. This explicitly handles the last-to-first seam. -/
theorem cyclicOwnerRunIndex_after_last_cut
    (owner : Fin n → Owner)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (t : Fin n)
    (hAfter : cyclicOwnerLastCut owner hCuts < t) :
    cyclicOwnerRunIndex owner hCuts t =
      (⟨0, hCuts⟩ : Fin (cyclicOwnerChanges owner)) := by
  classical
  have hLastIndex (j : Fin (cyclicOwnerChanges owner)) :
      j ≤ (⟨cyclicOwnerChanges owner - 1, by omega⟩ :
        Fin (cyclicOwnerChanges owner)) := by
    change j.val ≤ cyclicOwnerChanges owner - 1
    have := j.isLt
    omega
  have hNoRight : ¬ (cyclicOwnerRightCutIndices owner t).Nonempty := by
    rintro ⟨j, hj⟩
    have hRight : t ≤ cyclicOwnerCutIndex owner j :=
      (mem_cyclicOwnerRightCutIndices_iff owner t j).mp hj
    have hSourceLe : cyclicOwnerCutIndex owner j ≤
        cyclicOwnerLastCut owner hCuts :=
      (cyclicOwnerCutIndex owner).monotone (hLastIndex j)
    exact (not_le_of_gt hAfter) (hRight.trans hSourceLe)
  simp [cyclicOwnerRunIndex, hNoRight]

end StructuralRamsey.Girth

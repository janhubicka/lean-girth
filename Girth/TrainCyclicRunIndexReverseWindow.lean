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

end StructuralRamsey.Girth

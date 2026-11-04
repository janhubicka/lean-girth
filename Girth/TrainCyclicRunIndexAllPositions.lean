import Girth.TrainCyclicRunWrap
import Mathlib.Tactic

/-!
# Path A: a total canonical run index for every original occurrence

For a cyclic owner word with at least one cut, assign to each original
source position the least canonical indexed cut AT OR TO ITS RIGHT.
If the source position lies beyond the final linearly indexed cut,
assign it to the first indexed cut, correctly handling cyclic wrap.

The assignment is total and the owner at each original position
equals the owner of its assigned right-end cut. At a cut position the
assignment is exactly that cut's canonical index. These are the
missing literal source-position / reduced-run transport equations.

No chosen supreme plan, no appendix, no manuscript marker changes.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- Canonical cut indices whose physical cut is at or to the RIGHT
of the given source occurrence in the linear Fin n enumeration. -/
noncomputable def cyclicOwnerRightCutIndices
    (owner : Fin n → Owner) (t : Fin n) :
    Finset (Fin (cyclicOwnerChanges owner)) := by
  classical
  exact Finset.univ.filter
    (fun j => t ≤ cyclicOwnerCutIndex owner j)

theorem mem_cyclicOwnerRightCutIndices_iff
    (owner : Fin n → Owner) (t : Fin n)
    (j : Fin (cyclicOwnerChanges owner)) :
    j ∈ cyclicOwnerRightCutIndices owner t ↔
      t ≤ cyclicOwnerCutIndex owner j := by
  classical
  simp [cyclicOwnerRightCutIndices]

/-- The total source-to-reduced-run index. The least right-hand cut
owns the source occurrence; if no cut lies to its linear right, the
cyclic wrap run ends at indexed cut zero. -/
noncomputable def cyclicOwnerRunIndex
    (owner : Fin n → Owner)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (t : Fin n) : Fin (cyclicOwnerChanges owner) := by
  classical
  if h : (cyclicOwnerRightCutIndices owner t).Nonempty then
    exact (cyclicOwnerRightCutIndices owner t).min' h
  else
    exact ⟨0, hCuts⟩

/-- If a cut lies to the linear right, the selected run-ending cut
is genuinely at or to the right of the source position. -/
theorem cyclicOwnerRunIndex_right_bound
    (owner : Fin n → Owner)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (t : Fin n)
    (hExists : (cyclicOwnerRightCutIndices owner t).Nonempty) :
    t ≤ cyclicOwnerCutIndex owner
      (cyclicOwnerRunIndex owner hCuts t) := by
  classical
  have hEq : cyclicOwnerRunIndex owner hCuts t =
      (cyclicOwnerRightCutIndices owner t).min' hExists := by
    simp [cyclicOwnerRunIndex, hExists]
  rw [hEq]
  exact (mem_cyclicOwnerRightCutIndices_iff owner t _).mp
    (Finset.min'_mem _ hExists)

/-- The run-ending cut has the LEAST eligible canonical index.
This is the key fact excluding any intermediate source owner cut. -/
theorem cyclicOwnerRunIndex_le_of_right
    (owner : Fin n → Owner)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (t : Fin n)
    (j : Fin (cyclicOwnerChanges owner))
    (hRight : t ≤ cyclicOwnerCutIndex owner j) :
    cyclicOwnerRunIndex owner hCuts t ≤ j := by
  classical
  have hMem : j ∈ cyclicOwnerRightCutIndices owner t :=
    (mem_cyclicOwnerRightCutIndices_iff owner t j).mpr hRight
  have hExists : (cyclicOwnerRightCutIndices owner t).Nonempty :=
    ⟨j, hMem⟩
  have hEq : cyclicOwnerRunIndex owner hCuts t =
      (cyclicOwnerRightCutIndices owner t).min' hExists := by
    simp [cyclicOwnerRunIndex, hExists]
  rw [hEq]
  exact Finset.min'_le _ j hMem

/-- The source-to-run map restricts to the identity on all ACTUAL
canonical cuts, including the final-to-first wrap cut. -/
theorem cyclicOwnerRunIndex_at_cut
    (owner : Fin n → Owner)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (j : Fin (cyclicOwnerChanges owner)) :
    cyclicOwnerRunIndex owner hCuts
      (cyclicOwnerCutIndex owner j) = j := by
  let t := cyclicOwnerCutIndex owner j
  have hLe : cyclicOwnerRunIndex owner hCuts t ≤ j :=
    cyclicOwnerRunIndex_le_of_right owner hCuts t j (le_refl _)
  have hExists : (cyclicOwnerRightCutIndices owner t).Nonempty :=
    ⟨j, (mem_cyclicOwnerRightCutIndices_iff owner t j).mpr (le_refl _)⟩
  have hRight : t ≤ cyclicOwnerCutIndex owner
      (cyclicOwnerRunIndex owner hCuts t) :=
    cyclicOwnerRunIndex_right_bound owner hCuts t hExists
  have hGe : j ≤ cyclicOwnerRunIndex owner hCuts t := by
    by_contra hNo
    have hLt : cyclicOwnerRunIndex owner hCuts t < j :=
      lt_of_not_ge hNo
    have hStrict := (cyclicOwnerCutIndex owner).strictMono hLt
    change cyclicOwnerCutIndex owner
        (cyclicOwnerRunIndex owner hCuts t) < t at hStrict
    exact (not_lt_of_ge hRight) hStrict
  exact le_antisymm hLe hGe

/-- Every ORIGINAL source occurrence has exactly the geometric
owner represented by the assigned cut in the reduced witness word.
This proves both ordinary indexed runs and the cyclic wrap run.

No assumption that an original source label is itself a copy of
the reduced owner is made: this is equality of geometric OWNERS. -/
theorem cyclicOwnerRunIndex_owner_eq_cut
    (owner : Fin n → Owner)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (t : Fin n) :
    owner t =
      owner (cyclicOwnerCutIndex owner
        (cyclicOwnerRunIndex owner hCuts t)) := by
  classical
  by_cases hExists : (cyclicOwnerRightCutIndices owner t).Nonempty
  · have hUpper : t ≤ cyclicOwnerCutIndex owner
        (cyclicOwnerRunIndex owner hCuts t) :=
      cyclicOwnerRunIndex_right_bound owner hCuts t hExists
    apply cyclicOwner_constant_on_linear_interval
      owner t
      (cyclicOwnerCutIndex owner (cyclicOwnerRunIndex owner hCuts t))
      hUpper
    intro u htu huUpper
    by_contra hNe
    have huCut : u ∈ cyclicOwnerCutPositions owner :=
      (mem_cyclicOwnerCutPositions_iff owner u).mpr hNe
    obtain ⟨j, hj⟩ := (cyclicOwnerCutIndex_mem_iff owner u).mp huCut
    have hLe : cyclicOwnerRunIndex owner hCuts t ≤ j :=
      cyclicOwnerRunIndex_le_of_right owner hCuts t j (by
        rw [hj]
        exact htu)
    have hCutLe := (cyclicOwnerCutIndex owner).monotone hLe
    rw [hj] at hCutLe
    exact (not_le_of_gt huUpper) hCutLe
  · have hNone : ¬ ∃ j : Fin (cyclicOwnerChanges owner),
          t ≤ cyclicOwnerCutIndex owner j := by
      rintro ⟨j, hj⟩
      exact hExists
        ⟨j, (mem_cyclicOwnerRightCutIndices_iff owner t j).mpr hj⟩
    have hNotLast : ¬ t ≤ cyclicOwnerLastCut owner hCuts := by
      intro h
      exact hNone
        ⟨⟨cyclicOwnerChanges owner - 1, by omega⟩, h⟩
    have hTail : cyclicOwnerLastCut owner hCuts < t :=
      lt_of_not_ge hNotLast
    have hn : 0 < n := by
      have := (cyclicOwnerLastCut owner hCuts).isLt
      omega
    have hTailOwner :
        owner (cyclicSucc (cyclicOwnerLastCut owner hCuts)) =
          owner t :=
      cyclicOwner_constant_on_wrap_run owner hn hCuts t
        (Or.inl hTail)
    have hFirstOwner :
        owner (cyclicSucc (cyclicOwnerLastCut owner hCuts)) =
          owner (cyclicOwnerFirstCut owner hCuts) :=
      cyclicOwner_wrap_start_eq_first_cut owner hn hCuts
    have hIndex :
        cyclicOwnerRunIndex owner hCuts t =
          (⟨0, hCuts⟩ : Fin (cyclicOwnerChanges owner)) := by
      simp [cyclicOwnerRunIndex, hExists]
    rw [hIndex]
    change owner t = owner (cyclicOwnerFirstCut owner hCuts)
    exact hTailOwner.symm.trans hFirstOwner

end StructuralRamsey.Girth

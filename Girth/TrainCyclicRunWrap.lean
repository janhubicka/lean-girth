import Girth.TrainCyclicRunGaps
import Mathlib.Tactic

/-!
# Circulation: the wrap-around run and adjacent distinct owner labels

The ordinary indexed cut intervals are settled in
TrainCyclicRunGaps. This module handles the unique interval that
crosses the end of the linear Fin n order: from immediately AFTER
the last indexed cut back to the first indexed cut. We then obtain
a canonical reduced owner word with as many occurrences as actual
cuts, whose cyclically adjacent owners are genuinely different.

This is a correct abstract segmented OWNER word, not the labelled
witness BigCycle: physical connectors, distinct contracted wagons,
acceptability (A1--A3) and cyclic order comparison remain separate.
No appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- The first indexed actual owner cut. -/
noncomputable def cyclicOwnerFirstCut
    (owner : Fin n → Owner) (hk : 0 < cyclicOwnerChanges owner) : Fin n :=
  cyclicOwnerCutIndex owner ⟨0, hk⟩

/-- The last indexed actual owner cut, in the ordinary Fin order. -/
noncomputable def cyclicOwnerLastCut
    (owner : Fin n → Owner) (hk : 0 < cyclicOwnerChanges owner) : Fin n :=
  cyclicOwnerCutIndex owner
    ⟨cyclicOwnerChanges owner - 1, by omega⟩

/-- Since there are no cuts before the first indexed cut, ownership
does not change from the physical position 0 to that first cut. -/
theorem cyclicOwner_zero_eq_first_cut
    (owner : Fin n → Owner) (hn : 0 < n)
    (hk : 0 < cyclicOwnerChanges owner) :
    owner (⟨0, hn⟩ : Fin n) =
      owner (cyclicOwnerFirstCut owner hk) := by
  let zero : Fin n := ⟨0, hn⟩
  let first := cyclicOwnerFirstCut owner hk
  apply cyclicOwner_constant_on_linear_interval owner zero first
  · change 0 ≤ first.val
    omega
  · intro t _hlo hhi
    exact cyclicOwner_no_cut_before_first owner hk t hhi

/-- The tail following the last indexed cut connects through the
actual end-of-word successor to physical position 0. This is the
cyclic wrap case that a linearly indexed list alone cannot prove. -/
theorem cyclicOwner_last_cut_successor_eq_zero
    (owner : Fin n → Owner) (hn : 0 < n)
    (hk : 0 < cyclicOwnerChanges owner) :
    owner (cyclicSucc (cyclicOwnerLastCut owner hk)) =
      owner (⟨0, hn⟩ : Fin n) := by
  let last := cyclicOwnerLastCut owner hk
  let zero : Fin n := ⟨0, hn⟩
  by_cases hLast : last.val + 1 = n
  · have hs : cyclicSucc last = zero := by
      apply Fin.ext
      change (last.val + 1) % n = 0
      rw [hLast]
      exact Nat.mod_self n
    rw [hs]
  · have hBelow : last.val + 1 < n := by
      have := last.isLt
      omega
    let start : Fin n := ⟨last.val + 1, hBelow⟩
    let final : Fin n := ⟨n - 1, by omega⟩
    have hSucc : cyclicSucc last = start := by
      apply Fin.ext
      change (last.val + 1) % n = last.val + 1
      exact Nat.mod_eq_of_lt hBelow
    have hBounds : start ≤ final := by
      change last.val + 1 ≤ n - 1
      omega
    have hTail : owner start = owner final :=
      cyclicOwner_constant_on_linear_interval owner start final hBounds (by
        intro t hStart _hFinal
        have hLastLess : last < t := by
          change last.val < t.val
          have hStartVal : last.val + 1 ≤ t.val := hStart
          omega
        exact cyclicOwner_no_cut_after_last owner hk t hLastLess)
    have hFinalAbove : last < final := by
      change last.val < n - 1
      omega
    have hFinalNext : owner final = owner (cyclicSucc final) :=
      cyclicOwner_no_cut_after_last owner hk final hFinalAbove
    have hFinalSucc : cyclicSucc final = zero := by
      apply Fin.ext
      change (n - 1 + 1) % n = 0
      have hN : n - 1 + 1 = n := by omega
      rw [hN]
      exact Nat.mod_self n
    calc
      owner (cyclicSucc last) = owner start := by rw [hSucc]
      _ = owner final := hTail
      _ = owner zero := by rw [hFinalSucc] at hFinalNext; exact hFinalNext

/-- The entire wrap-around run has one owner, from just after the
last linearly indexed cut up through the first cut. -/
theorem cyclicOwner_wrap_start_eq_first_cut
    (owner : Fin n → Owner) (hn : 0 < n)
    (hk : 0 < cyclicOwnerChanges owner) :
    owner (cyclicSucc (cyclicOwnerLastCut owner hk)) =
      owner (cyclicOwnerFirstCut owner hk) :=
  (cyclicOwner_last_cut_successor_eq_zero owner hn hk).trans
    (cyclicOwner_zero_eq_first_cut owner hn hk)

/-- EVERY occurrence in the cyclic wrap interval shares the owner
at the successor of the last cut. The disjunction describes either
the linear tail or the linear head, including both endpoints. -/
theorem cyclicOwner_constant_on_wrap_run
    (owner : Fin n → Owner) (hn : 0 < n)
    (hk : 0 < cyclicOwnerChanges owner)
    (t : Fin n)
    (hIn : cyclicOwnerLastCut owner hk < t ∨
      t ≤ cyclicOwnerFirstCut owner hk) :
    owner (cyclicSucc (cyclicOwnerLastCut owner hk)) = owner t := by
  let last := cyclicOwnerLastCut owner hk
  let first := cyclicOwnerFirstCut owner hk
  rcases hIn with hTail | hHead
  · by_cases hLast : last.val + 1 = n
    · have hT := t.isLt
      have hLastT : last.val < t.val := hTail
      omega
    · have hBelow : last.val + 1 < n := by
        have := last.isLt
        omega
      let start : Fin n := ⟨last.val + 1, hBelow⟩
      have hs : cyclicSucc last = start := by
        apply Fin.ext
        change (last.val + 1) % n = last.val + 1
        exact Nat.mod_eq_of_lt hBelow
      have hStart : start ≤ t := by
        change last.val + 1 ≤ t.val
        have hh : last.val < t.val := hTail
        omega
      have hPath : owner start = owner t :=
        cyclicOwner_constant_on_linear_interval owner start t hStart (by
          intro u hStartU _hUT
          have hLastU : last < u := by
            change last.val < u.val
            have hu : last.val + 1 ≤ u.val := hStartU
            omega
          exact cyclicOwner_no_cut_after_last owner hk u hLastU)
      rw [hs]
      exact hPath
  · have hToFirst : owner t = owner first :=
      cyclicOwner_constant_on_linear_interval owner t first hHead (by
        intro u _hStart hBelow
        exact cyclicOwner_no_cut_before_first owner hk u hBelow)
    exact (cyclicOwner_wrap_start_eq_first_cut owner hn hk).trans
      hToFirst.symm

/-- In a finite CYCLIC word, exactly one change is impossible.
The proof checks the wrap, not just the linearly ordered prefix. -/
theorem cyclicOwner_changes_ne_one
    (owner : Fin n → Owner) (hn : 0 < n) :
    cyclicOwnerChanges owner ≠ 1 := by
  intro hOne
  have hk : 0 < cyclicOwnerChanges owner := by omega
  have hIdx : (⟨cyclicOwnerChanges owner - 1, by omega⟩ :
      Fin (cyclicOwnerChanges owner)) =
      (⟨0, hk⟩ : Fin (cyclicOwnerChanges owner)) := by
    apply Fin.ext
    change cyclicOwnerChanges owner - 1 = 0
    omega
  have hCut := cyclicOwnerCutIndex_is_change owner
    (⟨0, hk⟩ : Fin (cyclicOwnerChanges owner))
  have hWrap := cyclicOwner_wrap_start_eq_first_cut owner hn hk
  unfold cyclicOwnerLastCut cyclicOwnerFirstCut at hWrap
  rw [hIdx] at hWrap
  exact hCut hWrap.symm

/-- The abstract owner label of the maximal cyclic segment starting
immediately after the corresponding physical cut. -/
noncomputable def cyclicOwnerRunLabel
    (owner : Fin n → Owner)
    (i : Fin (cyclicOwnerChanges owner)) : Owner :=
  owner (cyclicSucc (cyclicOwnerCutIndex owner i))

/-- The owner of one segment equals the owner at the NEXT cyclic cut,
including the indexed last-to-first wrap. -/
theorem cyclicOwnerRunLabel_eq_next_cut
    (owner : Fin n → Owner)
    (i : Fin (cyclicOwnerChanges owner)) :
    cyclicOwnerRunLabel owner i =
      owner (cyclicOwnerCutIndex owner (cyclicSucc i)) := by
  have hk : 0 < cyclicOwnerChanges owner := by
    have := i.isLt
    omega
  by_cases hNext : i.val + 1 < cyclicOwnerChanges owner
  · have hs : cyclicSucc i =
        (⟨i.val + 1, hNext⟩ : Fin (cyclicOwnerChanges owner)) := by
      apply Fin.ext
      change (i.val + 1) % cyclicOwnerChanges owner = i.val + 1
      exact Nat.mod_eq_of_lt hNext
    rw [hs]
    unfold cyclicOwnerRunLabel
    have hlt : cyclicOwnerCutIndex owner i <
        cyclicOwnerCutIndex owner
          (⟨i.val + 1, hNext⟩ : Fin (cyclicOwnerChanges owner)) :=
      (cyclicOwnerCutIndex owner).strictMono (by
        change i.val < i.val + 1
        omega)
    exact cyclicOwner_constant_between_indexed_cuts owner i hNext
      (cyclicOwnerCutIndex owner ⟨i.val + 1, hNext⟩)
      hlt (le_refl _)
  · have hEnd : i.val + 1 = cyclicOwnerChanges owner := by
      have := i.isLt
      omega
    have hs : cyclicSucc i =
        (⟨0, hk⟩ : Fin (cyclicOwnerChanges owner)) := by
      apply Fin.ext
      change (i.val + 1) % cyclicOwnerChanges owner = 0
      rw [hEnd]
      exact Nat.mod_self _
    have hLast : i =
        (⟨cyclicOwnerChanges owner - 1, by omega⟩ :
          Fin (cyclicOwnerChanges owner)) := by
      apply Fin.ext
      change i.val = cyclicOwnerChanges owner - 1
      omega
    have hn : 0 < n := by
      have := (cyclicOwnerCutIndex owner i).isLt
      omega
    unfold cyclicOwnerRunLabel
    rw [hs, hLast]
    simpa [cyclicOwnerFirstCut, cyclicOwnerLastCut] using
      (cyclicOwner_wrap_start_eq_first_cut owner hn hk)

/-- Consecutive maximal-segment OWNER LABELS are different, including
the last-to-first pair. This is only an owner-level BigCycle field:
the map from standard owners into witness designated labels still
requires the intended concrete injective copy-index family. -/
theorem cyclicOwnerRunLabel_adjacent_ne
    (owner : Fin n → Owner)
    (i : Fin (cyclicOwnerChanges owner)) :
    cyclicOwnerRunLabel owner i ≠
      cyclicOwnerRunLabel owner (cyclicSucc i) := by
  rw [cyclicOwnerRunLabel_eq_next_cut owner i]
  unfold cyclicOwnerRunLabel
  exact cyclicOwnerCutIndex_is_change owner (cyclicSucc i)

end StructuralRamsey.Girth

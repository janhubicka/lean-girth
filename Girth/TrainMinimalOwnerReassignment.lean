import Girth.TrainCyclicOwnerRuns
import Mathlib.Tactic

/-!
# Minimal cyclic owners: an isolated owner cannot be reassigned to a neighbour

The finite part of the minimum-cut argument for bottom forest-to-system-girth.
Changing a single owner that has cuts on both sides cannot create a new cut.
If one old cut disappears, the total number of cyclic cuts strictly decreases.
Geometric admissibility of the new owner remains a separate hypothesis.
-/

namespace StructuralRamsey.Girth

universe v

/-- A single edit with two previous cuts and one eliminated cut strictly
decreases the actual cyclic change count, including the closing boundary. -/
theorem cyclicOwnerChanges_lt_of_isolated_edit
    {Owner : Type v} {n : Nat} (hn : 2 ≤ n)
    (before after : Fin n → Owner) (j : Fin n)
    (hLeft : before (trainCyclicPred j) ≠ before j)
    (hRight : before j ≠ before (cyclicSucc j))
    (hElse : ∀ k : Fin n, k ≠ j → after k = before k)
    (hClose : after (trainCyclicPred j) = after j ∨
      after j = after (cyclicSucc j)) :
    cyclicOwnerChanges after < cyclicOwnerChanges before := by
  classical
  let oldCuts := cyclicOwnerCutPositions before
  let newCuts := cyclicOwnerCutPositions after
  have hOldLeft : trainCyclicPred j ∈ oldCuts := by
    apply (mem_cyclicOwnerCutPositions_iff before _).2
    simpa only [cyclicSucc_trainCyclicPred_of_two_le hn j] using hLeft
  have hOldRight : j ∈ oldCuts :=
    (mem_cyclicOwnerCutPositions_iff before j).2 hRight
  have hSubset : newCuts ⊆ oldCuts := by
    intro k hk
    have hNewCut : after k ≠ after (cyclicSucc k) :=
      (mem_cyclicOwnerCutPositions_iff after k).1 hk
    by_cases hIsJ : k = j
    · subst k
      exact hOldRight
    · by_cases hSuccJ : cyclicSucc k = j
      · have hIsPred : k = trainCyclicPred j := by
          calc
            k = trainCyclicPred (cyclicSucc k) :=
              (trainCyclicPred_cyclicSucc_of_two_le hn k).symm
            _ = trainCyclicPred j := congrArg trainCyclicPred hSuccJ
        rw [hIsPred]
        exact hOldLeft
      · apply (mem_cyclicOwnerCutPositions_iff before k).2
        rw [hElse k hIsJ, hElse (cyclicSucc k) hSuccJ] at hNewCut
        exact hNewCut
  have hMissing : ∃ k : Fin n, k ∈ oldCuts ∧ k ∉ newCuts := by
    rcases hClose with hCloseLeft | hCloseRight
    · refine ⟨trainCyclicPred j, hOldLeft, ?_⟩
      intro hk
      exact ((mem_cyclicOwnerCutPositions_iff after _).1 hk) hCloseLeft
    · refine ⟨j, hOldRight, ?_⟩
      intro hk
      exact ((mem_cyclicOwnerCutPositions_iff after _).1 hk) hCloseRight
  obtain ⟨k, hkOld, hkNew⟩ := hMissing
  have hSubsetErase : newCuts ⊆ oldCuts.erase k := by
    intro a ha
    apply Finset.mem_erase.mpr
    constructor
    · intro hEq
      subst a
      exact hkNew ha
    · exact hSubset ha
  have hCard : newCuts.card < oldCuts.card :=
    lt_of_le_of_lt (Finset.card_le_card hSubsetErase)
      (Finset.card_erase_lt_of_mem hkOld)
  calc
    cyclicOwnerChanges after = newCuts.card :=
      (cyclicOwnerCutPositions_card after).symm
    _ < oldCuts.card := hCard
    _ = cyclicOwnerChanges before := cyclicOwnerCutPositions_card before

/-- An isolated occurrence in a minimal admissible owner assignment cannot
be given the admissible owner of either cyclic neighbour. -/
theorem minimalCyclicOwner_no_isolated_adjacent_reassignment
    {Owner : Type v} {n : Nat} (hn : 2 ≤ n)
    (allowed : Fin n → Owner → Prop)
    (owner : Fin n → Owner)
    (hAllowed : ∀ j : Fin n, allowed j (owner j))
    (hMin : ∀ other : Fin n → Owner,
      (∀ j : Fin n, allowed j (other j)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (j : Fin n)
    (hLeft : owner (trainCyclicPred j) ≠ owner j)
    (hRight : owner j ≠ owner (cyclicSucc j))
    (candidate : Owner) (hCandidate : allowed j candidate)
    (hAdjacent : candidate = owner (trainCyclicPred j) ∨
      candidate = owner (cyclicSucc j)) : False := by
  classical
  let edited : Fin n → Owner := Function.update owner j candidate
  have hAt : edited j = candidate := by simp [edited]
  have hElse (k : Fin n) (hk : k ≠ j) : edited k = owner k := by
    simp [edited, hk]
  have hAdmissible : ∀ k : Fin n, allowed k (edited k) := by
    intro k
    by_cases hk : k = j
    · subst k
      rw [hAt]
      exact hCandidate
    · rw [hElse k hk]
      exact hAllowed k
  have hPredNe : trainCyclicPred j ≠ j := by
    intro heq
    apply hLeft
    rw [heq]
  have hSuccNe : cyclicSucc j ≠ j := by
    intro heq
    apply hRight
    rw [heq]
  have hClose : edited (trainCyclicPred j) = edited j ∨
      edited j = edited (cyclicSucc j) := by
    rcases hAdjacent with hPrev | hNext
    · left
      calc
        edited (trainCyclicPred j) = owner (trainCyclicPred j) :=
          hElse _ hPredNe
        _ = candidate := hPrev.symm
        _ = edited j := hAt.symm
    · right
      calc
        edited j = candidate := hAt
        _ = owner (cyclicSucc j) := hNext
        _ = edited (cyclicSucc j) := (hElse _ hSuccNe).symm
  have hDrop := cyclicOwnerChanges_lt_of_isolated_edit
    hn owner edited j hLeft hRight hElse hClose
  exact (not_lt_of_ge (hMin edited hAdmissible)) hDrop

end StructuralRamsey.Girth

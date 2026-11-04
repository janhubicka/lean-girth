import Girth.TrainCyclicTwoRunOwnerBound
import Girth.TrainActualThreeCutNonadjacentLong
import Mathlib.Tactic

/-!
# Path A: strict decrease when a two-short receiving owner touches an outer run

The previously validated nonincrease theorem for simultaneous reassignment of
two consecutive occurrences is sharp in general. If the receiving owner is
ALREADY the owner immediately outside at least one end, however, that
boundary disappears and no new owner cut can appear.

The proof is an actual strict inclusion of the finite cyclic cut-position
sets, with wraparound covered. It is independent of physical edge labels
and is not a proof that such an exterior-owner match always exists.
No appendix or manuscript modification.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- Expose the cut-set inclusion underlying the verified two-run
nonincrease theorem. Both original OUTER boundaries are assumed cuts;
nothing is assumed about the original interior. -/
theorem cyclicOwnerCutPositions_replace_two_run_subset
    (hn : 2 ≤ n) (owner : Fin n → Owner)
    (t : Fin n) (a : Owner)
    (hPrev : owner (trainCyclicPred t) ≠ owner t)
    (hNext : owner (cyclicSucc t) ≠
      owner (cyclicSucc (cyclicSucc t))) :
    cyclicOwnerCutPositions (cyclicReplaceTwoOwners owner t a) ⊆
      cyclicOwnerCutPositions owner := by
  classical
  let changed := cyclicReplaceTwoOwners owner t a
  intro j hj
  have hNew := (mem_cyclicOwnerCutPositions_iff changed j).mp hj
  by_cases hJt : j = t
  · subst j
    have hEq : changed t = changed (cyclicSucc t) := by
      simp [changed, cyclicReplaceTwoOwners]
    exact False.elim (hNew hEq)
  · by_cases hJNext : j = cyclicSucc t
    · subst j
      exact (mem_cyclicOwnerCutPositions_iff owner (cyclicSucc t)).mpr hNext
    · by_cases hSuccT : cyclicSucc j = t
      · have hJPred : j = trainCyclicPred t := by
          have h := congrArg trainCyclicPred hSuccT
          rw [trainCyclicPred_cyclicSucc_of_two_le hn j] at h
          exact h
        apply (mem_cyclicOwnerCutPositions_iff owner j).mpr
        rw [hSuccT, hJPred]
        exact hPrev
      · have hSuccNeNext :
          cyclicSucc j ≠ cyclicSucc t := by
          intro hEq
          have h := congrArg trainCyclicPred hEq
          rw [trainCyclicPred_cyclicSucc_of_two_le hn j,
              trainCyclicPred_cyclicSucc_of_two_le hn t] at h
          exact hJt h
        apply (mem_cyclicOwnerCutPositions_iff owner j).mpr
        simpa [changed, cyclicReplaceTwoOwners,
          hJt, hJNext, hSuccT, hSuccNeNext] using hNew

/-- The TWO-RUN owner cut count decreases strictly if the
reassignment owner matches either original OUTSIDE neighbour.
This avoids an unjustified strict claim in the remaining case
of two physical labels and no neighbour match. -/
theorem cyclicOwnerChanges_replace_two_run_strict_of_outer_match
    (hn : 3 ≤ n) (owner : Fin n → Owner)
    (t : Fin n) (a : Owner)
    (hPrev : owner (trainCyclicPred t) ≠ owner t)
    (hNext : owner (cyclicSucc t) ≠
      owner (cyclicSucc (cyclicSucc t)))
    (hMatch : owner (trainCyclicPred t) = a ∨
      owner (cyclicSucc (cyclicSucc t)) = a) :
    cyclicOwnerChanges (cyclicReplaceTwoOwners owner t a) <
      cyclicOwnerChanges owner := by
  classical
  let changed := cyclicReplaceTwoOwners owner t a
  let newCuts := cyclicOwnerCutPositions changed
  let oldCuts := cyclicOwnerCutPositions owner
  have hSub : newCuts ⊆ oldCuts :=
    cyclicOwnerCutPositions_replace_two_run_subset
      (by omega : 2 ≤ n) owner t a hPrev hNext
  have hVanished : ∃ j : Fin n, j ∈ oldCuts ∧ j ∉ newCuts := by
    rcases hMatch with hLeft | hRight
    · refine ⟨trainCyclicPred t, ?_, ?_⟩
      · exact (mem_cyclicOwnerCutPositions_iff owner
          (trainCyclicPred t)).mpr hPrev
      · have hPredNe : trainCyclicPred t ≠ t := by
          intro heq
          have hs := cyclicSucc_trainCyclicPred_of_two_le
            (by omega : 2 ≤ n) t
          rw [heq] at hs
          exact (cyclicSucc_ne_self_of_two_le
            (by omega : 2 ≤ n) t) hs
        have hPredNeSucc : trainCyclicPred t ≠ cyclicSucc t := by
          intro heq
          have hs := congrArg cyclicSucc heq
          rw [cyclicSucc_trainCyclicPred_of_two_le
            (by omega : 2 ≤ n) t] at hs
          exact (cyclicSucc_succ_ne_self_of_three_le hn t) hs.symm
        have hAtPred : changed (trainCyclicPred t) = a := by
          simp [changed, cyclicReplaceTwoOwners,
            hPredNe, hPredNeSucc, hLeft]
        have hAtT : changed t = a := by
          simp [changed, cyclicReplaceTwoOwners]
        have hSuccPred : cyclicSucc (trainCyclicPred t) = t :=
          cyclicSucc_trainCyclicPred_of_two_le
            (by omega : 2 ≤ n) t
        intro hNew
        have hh := (mem_cyclicOwnerCutPositions_iff changed
          (trainCyclicPred t)).mp hNew
        rw [hSuccPred, hAtPred, hAtT] at hh
        exact hh rfl
    · refine ⟨cyclicSucc t, ?_, ?_⟩
      · exact (mem_cyclicOwnerCutPositions_iff owner
          (cyclicSucc t)).mpr hNext
      · have hTwoNotT :
            cyclicSucc (cyclicSucc t) ≠ t :=
          cyclicSucc_succ_ne_self_of_three_le hn t
        have hTwoNotSucc :
            cyclicSucc (cyclicSucc t) ≠ cyclicSucc t :=
          cyclicSucc_ne_self_of_two_le
            (by omega : 2 ≤ n) (cyclicSucc t)
        have hAtSucc : changed (cyclicSucc t) = a := by
          simp [changed, cyclicReplaceTwoOwners]
        have hAtTwo : changed (cyclicSucc (cyclicSucc t)) = a := by
          simp [changed, cyclicReplaceTwoOwners,
            hTwoNotT, hTwoNotSucc, hRight]
        intro hNew
        have hh := (mem_cyclicOwnerCutPositions_iff changed
          (cyclicSucc t)).mp hNew
        rw [hAtSucc, hAtTwo] at hh
        exact hh rfl
  have hNe : newCuts ≠ oldCuts := by
    intro hEq
    obtain ⟨j, hjOld, hjNew⟩ := hVanished
    exact hjNew (by rw [hEq]; exact hjOld)
  have hProper : newCuts ⊂ oldCuts := lt_of_le_of_ne hSub hNe
  have hCard : newCuts.card < oldCuts.card :=
    Finset.card_lt_card hProper
  calc
    cyclicOwnerChanges (cyclicReplaceTwoOwners owner t a) =
        newCuts.card := (cyclicOwnerCutPositions_card changed).symm
    _ < oldCuts.card := hCard
    _ = cyclicOwnerChanges owner := cyclicOwnerCutPositions_card owner

end StructuralRamsey.Girth

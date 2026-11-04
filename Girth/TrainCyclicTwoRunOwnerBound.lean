import Girth.TrainCyclicOwnerIsolatedNonincrease
import Mathlib.Tactic

/-!
# Path A: replacing a two-occurrence maximal owner run

The selected non-singleton long case reduces to two consecutive
source occurrences with one common geometric owner, bounded by
genuine source cuts on both outer sides. Reassigning BOTH occurrences
to ANY new owner cannot increase the number of cyclic owner cuts:
the interior remains uncut, and the only possibly changed outer
boundaries were already cuts.

This is the finite owner-cut part of the proposed two-short
lexicographic descent. It neither asserts physical admissibility
of the new owner nor a designated-label decrease. No appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- Reassign both positions t and cyclicSucc t to the same new owner;
all other positions retain their old owner. -/
def cyclicReplaceTwoOwners (owner : Fin n → Owner)
    (t : Fin n) (a : Owner) : Fin n → Owner :=
  fun j => if j = t ∨ j = cyclicSucc t then a else owner j

/-- If both OUTER boundaries of a pair of consecutive source
occurrences are owner cuts, reassigning those two occurrences to
one arbitrary new owner cannot create any new cut.

No interior-cut hypothesis is needed for nonincrease: the newly
assigned pair has no cut between its members regardless of the old
owners. This works with cyclic wrap and n=2 as well. -/
theorem cyclicOwnerChanges_replace_two_run_le
    (hn : 2 ≤ n) (owner : Fin n → Owner)
    (t : Fin n) (a : Owner)
    (hPrev : owner (trainCyclicPred t) ≠ owner t)
    (hNext : owner (cyclicSucc t) ≠
      owner (cyclicSucc (cyclicSucc t))) :
    cyclicOwnerChanges (cyclicReplaceTwoOwners owner t a) ≤
      cyclicOwnerChanges owner := by
  classical
  let changed := cyclicReplaceTwoOwners owner t a
  have hSub : cyclicOwnerCutPositions changed ⊆
      cyclicOwnerCutPositions owner := by
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
  have hCard := Finset.card_le_card hSub
  calc
    cyclicOwnerChanges (cyclicReplaceTwoOwners owner t a) =
        (cyclicOwnerCutPositions changed).card :=
      (cyclicOwnerCutPositions_card changed).symm
    _ ≤ (cyclicOwnerCutPositions owner).card := hCard
    _ = cyclicOwnerChanges owner := cyclicOwnerCutPositions_card owner

end StructuralRamsey.Girth

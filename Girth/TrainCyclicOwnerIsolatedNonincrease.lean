import Girth.TrainCyclicOwnerAbsorption

/-!
# Changing an isolated owner's label cannot increase geometric cuts

The checked predecessor/successor absorption lemmas require the new
owner to equal a neighbouring owner and then give STRICT descent.
A fresh-long insertion can be sourced from a supreme standard which
does not neighbour the replaced designated singleton, so that strict
premise is not automatic.

For every finite cyclic word, if one occurrence has different owners
on BOTH sides, assigning ANY replacement owner to that occurrence
cannot introduce a new cyclic cut: both affected boundaries were
already cuts. This is the useful non-increase result, not a claim
that arbitrary fresh-long insertions strictly decrease the minimum.

The separate n -> n+1 duplication (two consecutive occurrences
having the same new owner) and actual geometric admissibility still
need to be assembled. No appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- Reassigning an isolated occurrence to any target owner never
creates new cuts: both affected cyclic boundaries were already cuts.
The proof is an inclusion of the actual finite cut-position sets. -/
theorem cyclicOwnerChanges_replace_isolated_le
    (hn : 2 ≤ n) (owner : Fin n → Owner)
    (k : Fin n) (a : Owner)
    (hPrev : owner (trainCyclicPred k) ≠ owner k)
    (hNext : owner k ≠ owner (cyclicSucc k)) :
    cyclicOwnerChanges (cyclicReplaceOwner owner k a) ≤
      cyclicOwnerChanges owner := by
  classical
  let changed := cyclicReplaceOwner owner k a
  have hSub : cyclicOwnerCutPositions changed ⊆
      cyclicOwnerCutPositions owner := by
    intro j hj
    have hNew := (mem_cyclicOwnerCutPositions_iff changed j).mp hj
    by_cases hjk : j = k
    · subst j
      exact (mem_cyclicOwnerCutPositions_iff owner k).mpr hNext
    · by_cases hsk : cyclicSucc j = k
      · have hjPred : j = trainCyclicPred k := by
          have hh := congrArg trainCyclicPred hsk
          rw [trainCyclicPred_cyclicSucc_of_two_le hn j] at hh
          exact hh
        apply (mem_cyclicOwnerCutPositions_iff owner j).mpr
        rw [hsk, hjPred]
        exact hPrev
      · apply (mem_cyclicOwnerCutPositions_iff owner j).mpr
        simpa [changed, cyclicReplaceOwner, hjk, hsk] using hNew
  have hCard := Finset.card_le_card hSub
  calc
    cyclicOwnerChanges (cyclicReplaceOwner owner k a) =
        (cyclicOwnerCutPositions changed).card :=
      (cyclicOwnerCutPositions_card changed).symm
    _ ≤ (cyclicOwnerCutPositions owner).card := hCard
    _ = cyclicOwnerChanges owner := cyclicOwnerCutPositions_card owner

/-- A receiving owner matching one neighbour gives the previously
checked strict descent. This makes the exact extra requirement
visible in the interface rather than silently assuming it. -/
theorem cyclicOwnerChanges_replace_isolated_strict_of_neighbor
    (hn : 2 ≤ n) (owner : Fin n → Owner)
    (k : Fin n) (a : Owner)
    (hPrev : owner (trainCyclicPred k) ≠ owner k)
    (hNext : owner k ≠ owner (cyclicSucc k))
    (hAdjacent : owner (cyclicSucc k) = a ∨
      owner (trainCyclicPred k) = a) :
    cyclicOwnerChanges (cyclicReplaceOwner owner k a) <
      cyclicOwnerChanges owner := by
  rcases hAdjacent with hRight | hLeft
  · have hOld : owner k ≠ a := by
      rw [← hRight]
      exact hNext
    exact cyclicOwnerChanges_absorb_right
      hn owner k a hRight hOld hPrev
  · have hOld : owner k ≠ a := by
      rw [← hLeft]
      exact Ne.symm hPrev
    exact cyclicOwnerChanges_absorb_left
      hn owner k a hLeft hOld hNext

end StructuralRamsey.Girth

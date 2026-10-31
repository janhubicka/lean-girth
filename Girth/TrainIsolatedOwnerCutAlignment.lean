import Girth.TrainActualCoreSingletonConsecutiveCuts

/-!
# Every isolated owner (including a designated singleton) has adjacent cut indices

The earlier core-singleton theorem specialized the two consecutive cut
positions to a core-edge-labelled source occurrence. A designated
standard-owned singleton has the same combinatorial property: its
owner differs from both immediate neighbours. This finite lemma supplies
the precise boundary-index alignment required by the actual reduced
long-piece physical lift.

No minimization, designated-label provenance, or extra picture
geometry is assumed. This is ONLY the cut-index alignment step, not the
positive-cut descent theorem. Circulation, no appendix.
-/

namespace StructuralRamsey.Girth

universe v

/-- An occurrence whose owner differs from both cyclic neighbours is
bounded by two consecutive cut positions in the canonical enumeration,
including the wraparound case. Unlike the previous core singleton
specialization, the owner can be a designated standard. -/
theorem cyclicOwnerCutIndex_pred_of_isolated
    {Owner : Type v} {n : ℕ}
    (owner : Fin n → Owner) (hn : 2 ≤ n)
    (k : Fin n)
    (hPrev : owner (trainCyclicPred k) ≠ owner k)
    (hNext : owner k ≠ owner (cyclicSucc k)) :
    ∃ j : Fin (cyclicOwnerChanges owner),
      cyclicOwnerCutIndex owner j = k ∧
      cyclicOwnerCutIndex owner (trainCyclicPred j) =
        trainCyclicPred k := by
  have hPrevCut :
      trainCyclicPred k ∈ cyclicOwnerCutPositions owner := by
    apply (mem_cyclicOwnerCutPositions_iff owner (trainCyclicPred k)).mpr
    simpa only [cyclicSucc_trainCyclicPred_of_two_le hn k] using hPrev
  have hCurrentCut : k ∈ cyclicOwnerCutPositions owner := by
    exact (mem_cyclicOwnerCutPositions_iff owner k).mpr hNext
  exact cyclicOwnerCutIndex_pred_of_adjacent_cuts
    owner hn k hPrevCut hCurrentCut

end StructuralRamsey.Girth

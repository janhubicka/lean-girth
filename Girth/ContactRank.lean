import Girth.TrainCutoffWellFounded
import Girth.RefinementRunCount

/-! Numerical changes from the old q-1 recursion to the new
k = max 2 (q / 2) recursion, with an arbitrary number of inserted levels. -/

namespace StructuralRamsey.Girth

theorem contact_refinement_cutoff_lt (q : ℕ) (hq : 2 < q) :
    max 2 (q / 2) < q := by
  apply max_lt_iff.mpr
  exact ⟨hq, by omega⟩

theorem contact_rank_drop (q k d : ℕ) (tail : List ℕ) (hk : k < q) :
    TrainCutoffRankDrop (q :: tail) (List.replicate d k ++ tail) q := by
  constructor
  · intro j hj
    have hkj : k ≠ j := by omega
    have hqj : q ≠ j := by omega
    rw [countTrainCutoff_append, countTrainCutoff_replicate_ne k j d hkj]
    simp [hqj]
  · have hkq : k ≠ q := by omega
    rw [countTrainCutoff_append, countTrainCutoff_replicate_ne k q d hkq]
    simp

theorem contact_refinement_rank_decreases (M q d : ℕ) (tail : List ℕ)
    (hq : 2 < q) (hBound : q ≤ M) :
    TrainCountLex M
      (List.replicate d (max 2 (q / 2)) ++ tail) (q :: tail) :=
  (contact_rank_drop q (max 2 (q / 2)) d tail
    (contact_refinement_cutoff_lt q hq)).toTrainCountLex
      _ _ q (by omega) M hBound

theorem contact_run_length_gt_two_g_plus_one (g : ℕ) (runs : List ℕ)
    (hAtLeastTwo : ∀ n ∈ runs, 2 ≤ n) (hManyRuns : g + 1 ≤ runs.length) :
    2*g+1 < runs.sum := by
  have h := refinementRun_length_ge_two_g_plus_two g runs hAtLeastTwo hManyRuns
  omega

end StructuralRamsey.Girth

import Girth.TrainCutoffWellFounded

/-! The exact recursive rank decrease in the new manuscript.
The replacement cutoff is max(2,q/2), not the older q-1.
The number of inserted levels is unrestricted. -/

namespace StructuralRamsey.Girth

def contactRefinementCutoff (q : ℕ) : ℕ := max 2 (q/2)

theorem contactRefinementCutoff_bounds {q : ℕ} (hq : 2 < q) :
    2 ≤ contactRefinementCutoff q ∧ contactRefinementCutoff q < q ∧
      q ≤ 2 * contactRefinementCutoff q + 1 := by
  unfold contactRefinementCutoff
  have hdiv : q/2 < q := by omega
  have htwo : 2 ≤ max 2 (q/2) := le_max_left _ _
  have hhalf : q/2 ≤ max 2 (q/2) := le_max_right _ _
  exact ⟨htwo,max_lt_iff.mpr ⟨hq,hdiv⟩,by omega⟩

/-- Any lower cutoff can replace the first coordinate arbitrarily
many times and still decrease the actual well-founded rank. -/
theorem contact_lowerReplacement_rankDrop
    (q k d : ℕ) (tail : List ℕ) (hk : k < q) :
    TrainCutoffRankDrop (q :: tail) (List.replicate d k ++ tail) q := by
  constructor
  · intro j hj
    rw [countTrainCutoff_append,countTrainCutoff_replicate_ne k j d (by omega)]
    simp [show q ≠ j by omega]
  · rw [countTrainCutoff_append,countTrainCutoff_replicate_ne k q d (by omega)]
    simp

theorem contact_refinement_rankDecrease
    (M q d : ℕ) (tail : List ℕ) (hq : 2 < q) (hM : q ≤ M) :
    TrainCountLex M
      (List.replicate (d-1) (contactRefinementCutoff q) ++ tail) (q :: tail) :=
  (contact_lowerReplacement_rankDrop q (contactRefinementCutoff q) (d-1) tail
    (contactRefinementCutoff_bounds hq).2.1).toTrainCountLex
    _ _ q (by omega) M hM

theorem contact_cutoffTwo_rankDecrease (M : ℕ) (tail : List ℕ) (hM : 2 ≤ M) :
    TrainCountLex M tail (2 :: tail) :=
  trainCutoffDropTwo_wfRankDecrease M tail hM

end StructuralRamsey.Girth

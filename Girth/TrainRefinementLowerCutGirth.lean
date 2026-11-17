import Girth.TrainRecursiveCutoffIndexAlignment
import Girth.TrainRecursiveParentChildCutGirth
import Girth.TrainRecursiveRefinementRetainedCutGirth

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe v
variable {E X P : Type v}

/-- The first retained cut controls the inserted prefix, including equality.
Every later cut retains its original threshold. This requires only labelled
cut girth and the actual refinement on the same edge family. -/
theorem refinedLabelledGirth_replicatedCutoffs
    {q : ℕ} {tail : List ℕ} {g : ℕ} (hg : 2 ≤ g)
    {T : EdgeTrainLevels E (q :: tail).length}
    {edge : E → Set X} {part : X → P} {firstAllowed : Set P}
    (R : FirstWagonRefinement T (by simp) edge part firstAllowed g)
    (hFirst : LabelledGirthGT (T.wagonClassCarrier edge ⟨1, by simp⟩) g)
    (hTail : ∀ j : Fin (q :: tail).length, 0 < j.val →
      LabelledGirthGT (T.wagonClassCarrier edge j.castSucc) ((q :: tail).get j)) :
    ∀ j : Fin ((q :: tail).length + R.extraCuts),
      LabelledGirthGT (R.train.wagonClassCarrier edge j.castSucc)
        ((List.replicate (R.extraCuts + 1) g ++ tail).get
          (Fin.cast (by simp [List.length_replicate]; omega) j)) := by
  intro j
  let d := R.extraCuts + 1
  let low := List.replicate d g ++ tail
  by_cases hInserted : j.val < d
  · have hCutoff : low.get (Fin.cast (by simp [low, d]; omega) j) = g := by
      exact replicatedCutoff_at_inserted g d tail ⟨j.val, hInserted⟩
    change LabelledGirthGT (R.train.wagonClassCarrier edge j.castSucc)
      (low.get (Fin.cast (by simp [low, d]; omega) j))
    rw [hCutoff]
    have hRetained : LabelledGirthGT
        (R.train.wagonClassCarrier edge ⟨R.extraCuts + 1, by simp⟩) g := by
      have hShift : EdgeTrainLevels.firstRefinementShift (q :: tail).length
          R.extraCuts ⟨1, by simp⟩ = ⟨R.extraCuts + 1, by simp⟩ := by
        apply Fin.ext
        change 1 + R.extraCuts = R.extraCuts + 1
        omega
      rw [← hShift]
      exact R.labelledGirthGT_at_retained ⟨1, by simp⟩ (Nat.zero_lt_succ 0) g hFirst
    exact R.labelledCutGirth_inserted_of_retained hg hRetained j.castSucc
      (Nat.le_of_lt hInserted)
  · have hPast : d ≤ j.val := Nat.le_of_not_lt hInserted
    let k : Fin tail.length := ⟨j.val - d, by
      have hlt := j.isLt
      dsimp [d] at hPast ⊢
      simp only [List.length_cons] at hlt
      omega⟩
    let old : Fin (q :: tail).length := ⟨k.val + 1, by simpa using Nat.succ_lt_succ k.isLt⟩
    have hIndex : EdgeTrainLevels.firstRefinementShift
        (q :: tail).length R.extraCuts old.castSucc = j.castSucc := by
      apply Fin.ext
      change j.val - d + 1 + R.extraCuts = j.val
      dsimp [d] at hPast ⊢
      omega
    have hCutoff : low.get (Fin.cast (by simp [low, d]; omega) j) = tail.get k := by
      have hIdx : (Fin.cast (by simp [low, d]; omega) j : Fin low.length) =
          ⟨d + k.val, by simpa [low] using Nat.add_lt_add_left k.isLt d⟩ := by
        apply Fin.ext
        change j.val = d + (j.val - d)
        omega
      rw [hIdx]
      exact replicatedCutoff_at_retained g d tail k
    change LabelledGirthGT (R.train.wagonClassCarrier edge j.castSucc)
      (low.get (Fin.cast (by simp [low, d]; omega) j))
    rw [hCutoff, ← hIndex]
    exact R.labelledGirthGT_at_retained old.castSucc (by change 0 < k.val + 1; omega)
      ((q :: tail).get old) (hTail old (by change 0 < k.val + 1; omega))

end StructuralRamsey.Girth.TrainRecursiveWitness

import Girth.TrainRecursiveTrueActiveRetainedTailCuts
import Girth.TrainRecursiveCutoffIndexAlignment

set_option autoImplicit false
set_option Elab.async false

/-!
# The complete lower recursive cutoff vector has its true labelled girth inputs

The lower q>2 request replaces t = q :: tail by
  List.replicate (extraCuts + 1) (q - 1) ++ tail.
The physical first-wagon refinement has exactly the corresponding
height. Positive fine indices below extraCuts+1 are inserted prefix
cuts of threshold q-1, whereas indices at or above that boundary are
retained positive OLD tail cuts with their full original thresholds.

We use the two genuine geometric theorems:
* global induced inserted-cut girth >q-1, already on main;
* full induced retained-tail cut girth >t[j] for each old positive j.

This is deliberately about the EXACT numerical list supplied to
the recursive lower witness. It introduces no independent cut
certificate, HJ-power girth assertion or edge pruning. It does not
claim the existence of the recursive Ramsey witness.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain :
  EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

/-- The literal replicated-prefix lower cutoff list has exactly the
height of a first-wagon refinement of the original nonempty train. -/
theorem lowerReplacementCutoff_length (q d : ℕ) (tail : List ℕ) :
    (List.replicate (d + 1) (q - 1) ++ tail).length =
      (q :: tail).length + d := by
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- Every positive fine train level satisfies the EXACT numerical
lower-rank cutoff at its literal list coordinate. The first retained
coordinate uses the first element of tail, not an inserted q-1 bound.
The equality cut is deliberately excluded: the lower initial-stage
constructor uses its ordinary full physical support girth instead. -/
theorem ForestTailStage.trueActive_inducedAllLowerCutGirth
    (stage : ForestTailStage A B D family (q :: tail)
      targetTrain allowed)
    (e : Embedding A D)
    (ht : Admissible (q :: tail)) (hq : 2 < q)
    (R : FirstWagonRefinement
      (stage.train.restrict
        (sharedOldACarrierInclusion A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding)))
      (by simp : 0 < (q :: tail).length)
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
      stage.system.part
      (allowed ⟨1, by simp⟩) (q - 1))
    (j : Fin ((q :: tail).length + R.extraCuts))
    (hj : 0 < j.val) :
    LabelledGirthGT
      ((R.train.restrict
        (inducedACarrierToShared A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding))).wagonClassCarrier
        (fun edge : OldACarrierEdge A
          (stage.system.toRelStructure.induce
            (activeCarrier A stage.system e.toFunctionEmbedding)) => edge.1)
        j.castSucc)
      ((List.replicate (R.extraCuts + 1) (q - 1) ++ tail).get
        ⟨j.val, by
          rw [lowerReplacementCutoff_length]
          exact j.isLt⟩) := by
  let d : ℕ := R.extraCuts + 1
  let lower : List ℕ := List.replicate d (q - 1) ++ tail
  have hLen : lower.length = (q :: tail).length + R.extraCuts := by
    simpa only [d, lower] using
      lowerReplacementCutoff_length q R.extraCuts tail
  let jLower : Fin lower.length := ⟨j.val, by rw [hLen]; exact j.isLt⟩
  change LabelledGirthGT
    ((R.train.restrict
      (inducedACarrierToShared A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding))).wagonClassCarrier
      (fun edge : OldACarrierEdge A
        (stage.system.toRelStructure.induce
          (activeCarrier A stage.system e.toFunctionEmbedding)) => edge.1)
      j.castSucc) (lower.get jLower)
  by_cases hInserted : j.val < d
  · let k : Fin d := ⟨j.val, hInserted⟩
    have hCutoff : lower.get jLower = q - 1 := by
      have h := replicatedCutoff_at_inserted (q - 1) d tail k
      simpa only [lower, jLower, k] using h
    rw [hCutoff]
    exact stage.trueActive_inducedInsertedCutGirth e ht
      (by simp : 0 < (q :: tail).length) hq R j.castSucc (by
        change j.val ≤ R.extraCuts + 1
        dsimp [d] at hInserted
        omega)
  · have hPast : d ≤ j.val := Nat.le_of_not_lt hInserted
    let k : Fin tail.length := ⟨j.val - d, by
      have hlt := j.isLt
      change j.val < (q :: tail).length + R.extraCuts at hlt
      simp only [List.length_cons] at hlt
      dsimp [d] at hPast ⊢
      omega⟩
    let old : Fin (q :: tail).length := ⟨k.val + 1, by
      change k.val + 1 < tail.length + 1
      exact Nat.succ_lt_succ k.isLt⟩
    have hOldPos : 0 < old.val := by
      change 0 < k.val + 1
      omega
    have hIdx :
        EdgeTrainLevels.firstRefinementShift
          (q :: tail).length R.extraCuts old.castSucc =
            j.castSucc := by
      apply Fin.ext
      change old.val + R.extraCuts = j.val
      change k.val + 1 + R.extraCuts = j.val
      change (j.val - d) + 1 + R.extraCuts = j.val
      dsimp [d] at hPast ⊢
      omega
    have hCutoff : lower.get jLower = (q :: tail).get old := by
      have hk : jLower =
          (⟨d + k.val, by
            simp only [lower, List.length_append, List.length_replicate]
            have hlt := k.isLt
            omega⟩ : Fin lower.length) := by
        apply Fin.ext
        change j.val = d + (j.val - d)
        omega
      rw [hk]
      calc
        lower.get (⟨d + k.val, by
            simp only [lower, List.length_append, List.length_replicate]
            omega⟩ : Fin lower.length) =
            tail.get k := by
              exact replicatedCutoff_at_retained (q - 1) d tail k
        _ = (q :: tail).get old := by
              change tail[k.val] = (q :: tail)[k.val + 1]
              simp
    rw [hCutoff, ← hIdx]
    exact stage.trueActive_inducedRetainedTailCutGirth e
      (by simp : 0 < (q :: tail).length) R old hOldPos

end StructuralRamsey.Girth.TrainRecursiveWitness

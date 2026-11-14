import Girth.TrainRecursiveTrueActiveRefinementCutGirth
import Girth.TrainRecursiveTrueActiveRetainedTailCuts

set_option autoImplicit false
set_option Elab.async false

/-!
# Track 6: complete global labelled-cut vector for a genuine refinement

The former child-by-child theorem already proves global bounds at
EVERY inserted cut. The old stage's tail certificates, transported
through exact retained quotient equivalences, provide EACH remaining
proper positive cut at its own original cutoff.

Here we combine these certified components for an arbitrary pointwise
requested cutoff function. The theorem neither constructs a Ramsey
witness nor assumes a new global fine-girth bound: its inputs are the
actual old stage, its first-wagon refinement, admissibility, and
the two elementary pointwise comparisons to the lower target vector.

This is an uncompiled candidate; run the exact-head axiom gate before
promoting its validation status.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
universe u v

variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- A genuine active refinement has global labelled-cut girth at
ALL proper fine levels, with the exact requested cutoffs. The
only cutoff comparisons are the componentwise numerical ones
for the inserted head and the retained old positive tail. -/
theorem ForestTailStage.trueActive_sharedFineCutVector
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D) (ht : Admissible t)
    (hm : 0 < t.length) (hq : 2 < t.headD 0)
    (R : FirstWagonRefinement
      (stage.train.restrict
        (sharedOldACarrierInclusion A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding)))
      hm
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
      stage.system.part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩)
      (t.headD 0 - 1))
    (cutoff : Fin (t.length + R.extraCuts + 1) → ℕ)
    (hInserted : ∀ ρ : Fin (t.length + R.extraCuts + 1),
      ρ.val ≤ R.extraCuts → cutoff ρ ≤ t.headD 0 - 1)
    (hRetained : ∀ j : Fin t.length, 0 < j.val →
      cutoff (EdgeTrainLevels.firstRefinementShift
        t.length R.extraCuts j.castSucc) ≤ t.get j)
    (ρ : Fin (t.length + R.extraCuts + 1))
    (hProper : ρ.val < t.length + R.extraCuts) :
    LabelledGirthGT
      (R.train.wagonClassCarrier
        (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
        ρ) (cutoff ρ) := by
  by_cases hPrefix : ρ.val ≤ R.extraCuts
  · exact labelledGirthGT_mono
      (stage.trueActive_sharedInsertedCutGirth e ht hm hq R ρ (by omega))
      (hInserted ρ hPrefix)
  · let j : Fin t.length := ⟨ρ.val - R.extraCuts, by omega⟩
    have hj : 0 < j.val := by
      dsimp [j]
      omega
    have hShift :
        EdgeTrainLevels.firstRefinementShift
          t.length R.extraCuts j.castSucc = ρ := by
      apply Fin.ext
      change j.val + R.extraCuts = ρ.val
      dsimp [j]
      omega
    have hCut : LabelledGirthGT
        (R.train.wagonClassCarrier
          (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
            (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
          ρ) (t.get j) := by
      simpa only [hShift] using
        (stage.trueActive_sharedRetainedTailCutGirth e hm R j hj)
    exact labelledGirthGT_mono hCut
      (by simpa only [hShift] using hRetained j hj)

end StructuralRamsey.Girth.TrainRecursiveWitness

#print axioms StructuralRamsey.Girth.TrainRecursiveWitness.ForestTailStage.trueActive_sharedFineCutVector

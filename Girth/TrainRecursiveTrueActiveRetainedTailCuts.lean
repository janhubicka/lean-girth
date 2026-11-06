import Girth.TrainRecursiveTrueActiveRefinementCutGirth

set_option autoImplicit false
set_option Elab.async false

/-!
# All genuinely retained tail cuts keep their original full thresholds

The q>2 lower target has inserted prefix cuts with threshold q-1
and retained positive old cuts with their OWN original thresholds t[j].
The first retained wagon cut can require a strictly stronger threshold
than q-1; the inserted cut proof alone does not supply it.

For every old positive tail index j, the old ForestTailStage.tailGirth
already supplies the full labelled horizontal bound at t[j]. The
verified physical active-source restriction gives this bound for all
shared A-edges. A genuine FirstWagonRefinement identifies exactly
each old positive cut with its shifted fine coordinate, and the
physical induced-source inclusion preserves labelled girth at the
same threshold.

This theorem makes no high-girth assertion about Hales--Jewett powers,
and neither changes edge labels nor deletes any edges of the
genuine induced active source.
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

/-- The COMPLETE shared physical old A-edge wagon cut retains every
original positive tail threshold t[j] in the actual fine refinement. -/
theorem ForestTailStage.trueActive_sharedRetainedTailCutGirth
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D) (hm : 0 < t.length)
    (R : FirstWagonRefinement
      (stage.train.restrict
        (sharedOldACarrierInclusion A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding)))
      hm
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
      stage.system.part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩) (t.headD 0 - 1))
    (j : Fin t.length) (hj : 0 < j.val) :
    LabelledGirthGT
      (R.train.wagonClassCarrier
        (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
        (EdgeTrainLevels.firstRefinementShift
          t.length R.extraCuts j.castSucc)) (t.get j) := by
  exact R.labelledGirthGT_at_retained
    j.castSucc (by change 0 < j.val; exact hj) (t.get j)
    (stage.trueActive_sharedTailCutGirth e j hj)

/-- The same ORIGINAL tail threshold on the complete physical A-edge
train of the TRUE induced active relational source. The original wagon
labels and all of their cut distinctions remain literal. -/
theorem ForestTailStage.trueActive_inducedRetainedTailCutGirth
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D) (hm : 0 < t.length)
    (R : FirstWagonRefinement
      (stage.train.restrict
        (sharedOldACarrierInclusion A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding)))
      hm
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
      stage.system.part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩) (t.headD 0 - 1))
    (j : Fin t.length) (hj : 0 < j.val) :
    LabelledGirthGT
      ((R.train.restrict
        (inducedACarrierToShared A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding))).wagonClassCarrier
        (fun edge : OldACarrierEdge A
          (stage.system.toRelStructure.induce
            (activeCarrier A stage.system e.toFunctionEmbedding)) => edge.1)
        (EdgeTrainLevels.firstRefinementShift
          t.length R.extraCuts j.castSucc)) (t.get j) := by
  exact trueActive_inducedCutGirth_of_shared A stage.system
    e.toFunctionEmbedding R.train
    (EdgeTrainLevels.firstRefinementShift t.length R.extraCuts j.castSucc)
    (t.get j)
    (stage.trueActive_sharedRetainedTailCutGirth e hm R j hj)

end StructuralRamsey.Girth.TrainRecursiveWitness

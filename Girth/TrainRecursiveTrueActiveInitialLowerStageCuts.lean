import Girth.TrainRecursiveTrueActiveInitialLowerStage
import Girth.TrainRecursiveTrueActiveLowerCutoffVector

set_option autoImplicit false
set_option Elab.async false

/-!
# Genuine initial lower stage without independently assumed positive cut girth

The old q>2 ForestTailStage and an actual FirstWagonRefinement already
supply EVERY positive labelled horizontal-cut girth certificate at the
literal lower cutoff vector, by the merged, axiom-audited
trueActive_inducedAllLowerCutGirth theorem. The old complete bottom mixed
forest supplies ordinary source support girth and the actual source
coverage. The verified initial-stage constructor therefore needs no
separate positive-cut-girth hypothesis.

Only full fine target AdjacentParameters and the concrete finite
part-preserving larger base/family remain explicit at this interface.
The lower recursive Ramsey witness, picture pass and attached-output
SupremeCycleBound are NOT constructed here. This is circulation only.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P Y : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain :
  EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

/-- The actual lower initial forest stage without a postulated lower
labelled-cut certificate. Cut girth comes from #899, and ordinary support
girth from the original mixed forest. Full fine AdjacentParameters
remain an explicit construction obligation until #888 is certified. -/
theorem ForestTailStage.exists_initialLowerStage_of_activeRefinement
    (stage : ForestTailStage A B D family (q :: tail)
      targetTrain allowed)
    (hA : A.Irreducible) [Nonempty UA]
    (e : Embedding A D)
    (projected : StructuralRamsey.Partite.ProjectedEmbedding A
      stage.system e.toFunctionEmbedding)
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
    (Large : StructuralRamsey.Partite.System L UA Y) [Finite Y]
    (lowerFamily : Set (Embedding
      (actualActiveSubsystemPartite A stage.system
        e.toFunctionEmbedding).toRelStructure
      Large.toRelStructure))
    [Nonempty lowerFamily]
    (hFamilyParts : ∀ b, b ∈ lowerFamily →
      ∀ x : activeCarrier A stage.system e.toFunctionEmbedding,
        Large.part (b x) =
          (actualActiveSubsystemPartite A stage.system
            e.toFunctionEmbedding).part x)
    (hFineParameters :
      (R.train.restrict
        (inducedACarrierToShared A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding))).AdjacentParameters
        (fun edge : OldACarrierEdge A
          (actualActiveSubsystemPartite A stage.system
            e.toFunctionEmbedding).toRelStructure => edge.1)
        (fun ρ =>
          (actualActiveSubsystemPartite A stage.system
            e.toFunctionEmbedding).part ⁻¹'
              (fineAllowedFromRefinement
                (q :: tail).length R.extraCuts
                (by simp : 0 < (q :: tail).length)
                e.toFunctionEmbedding allowed R.permitted ρ)))
    ∃ hLen : (q :: tail).length + R.extraCuts =
        (List.replicate (R.extraCuts + 1) (q - 1) ++ tail).length,
      Nonempty
        (ForestTailStage A
          (actualActiveSubsystemPartite A stage.system
            e.toFunctionEmbedding).toRelStructure
          Large.toRelStructure lowerFamily
          (List.replicate (R.extraCuts + 1) (q - 1) ++ tail)
          ((R.train.restrict
            (inducedACarrierToShared A stage.system.toRelStructure
              (activeCarrier A stage.system e.toFunctionEmbedding))).castHeight hLen)
          (fun ρ => Large.part ⁻¹'
            (fineAllowedFromRefinement
              (q :: tail).length R.extraCuts
              (by simp : 0 < (q :: tail).length)
              e.toFunctionEmbedding allowed R.permitted
              (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm ρ)))) := by
  apply stage.exists_initialLowerStage_of_activeTargetCuts
    hA e projected ht hq R Large lowerFamily hFamilyParts hFineParameters
  intro j hj
  exact stage.trueActive_inducedAllLowerCutGirth e ht hq R j hj

end StructuralRamsey.Girth.TrainRecursiveWitness

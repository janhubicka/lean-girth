import Girth.TrainRecursiveExactHeightTransport
import Girth.TrainRecursivePartiteBaseInitial
import Girth.TrainRecursiveTrueActiveTargetSupportData
import Girth.TrainRecursiveCanonicalFineAllowed

set_option autoImplicit false
set_option Elab.async false

/-!
# Initial lower forest stage from a genuine active refined target

The old ForestTailStage and one genuine projected active A-copy already
provide ordinary source support girth, physical support nonemptiness
and coverage of ALL active vertices.  A finite larger A-partite
Ramsey base with a part-preserving prescribed target family then
supports the ACTUAL initial lower ForestTailStage.

The lower cutoff vector has length equal to the true refined train
height, but the two arithmetic expressions are not definitionally
equal.  We use exact train-height equality transport rather than
replacing any physical edge labels, quotient wagons or relations.

The ONLY outstanding hypotheses here are full target adjacent
parameters and labelled positive cut bounds on the genuine
first-refined active source.  Track B #888 and #899 are intended
to discharge these.  This is an INITIAL stage construction; it does
not claim the lower finite Ramsey pass, partite arrow, or attached
output SupremeCycleBound.
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

/-- Construct the real initial lower stage from the true active target.

No support, girth or stage-existence assumptions are introduced beyond
the actual old stage and a projected A-copy.  The precise remaining
fine target parameter and positive-cut certificates are explicit until
their independent formalizations are CI-certified. The result records
the equality of the refined train height with the literal lower vector
height, and constructs a ForestTailStage with that EXACT train. -/
theorem ForestTailStage.exists_initialLowerStage_of_activeTargetCuts
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
    (hFineCuts :
      ∀ j : Fin ((q :: tail).length + R.extraCuts),
        0 < j.val →
          LabelledGirthGT
            ((R.train.restrict
              (inducedACarrierToShared A stage.system.toRelStructure
                (activeCarrier A stage.system e.toFunctionEmbedding))).wagonClassCarrier
              (fun edge : OldACarrierEdge A
                (actualActiveSubsystemPartite A stage.system
                  e.toFunctionEmbedding).toRelStructure => edge.1)
              j.castSucc)
            ((List.replicate (R.extraCuts + 1) (q - 1) ++ tail).get
              ⟨j.val, by
                simp only [List.length_append, List.length_replicate,
                  List.length_cons]
                have hj := j.isLt
                simp only [List.length_cons] at hj
                omega⟩)) :
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
  classical
  let Source := actualActiveSubsystemPartite A stage.system
    e.toFunctionEmbedding
  let lower := List.replicate (R.extraCuts + 1) (q - 1) ++ tail
  have hLen : (q :: tail).length + R.extraCuts = lower.length := by
    simp only [lower, List.length_append, List.length_replicate,
      List.length_cons]
    omega
  refine ⟨hLen, ?_⟩
  let FineTrain := (R.train.restrict
    (inducedACarrierToShared A stage.system.toRelStructure
      (activeCarrier A stage.system e.toFunctionEmbedding))).castHeight hLen
  let allowedFine : Fin (lower.length + 1) → Set UA :=
    fun ρ => fineAllowedFromRefinement
      (q :: tail).length R.extraCuts
      (by simp : 0 < (q :: tail).length)
      e.toFunctionEmbedding allowed R.permitted
      (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm ρ)
  letI : Finite stage.Vertex := stage.finiteVertex
  have htLower : Admissible lower :=
    ht.replace hq (Nat.zero_lt_succ R.extraCuts)
  have hHead : lower.headD 0 = q - 1 := by
    simp [lower, List.replicate_succ]
  have hSupport := stage.trueActive_initialSupportData
    e projected (q - 1) (by simp : q - 1 ≤ (q :: tail).headD 0)
  have hGirth : GirthGT (supportCopies A Source.toRelStructure)
      (lower.headD 0) := by
    rw [hHead]
    exact hSupport.2.2
  have hParams : FineTrain.AdjacentParameters
      (fun edge : OldACarrierEdge A Source.toRelStructure => edge.1)
      (fun ρ => Source.part ⁻¹' allowedFine ρ) := by
    exact (R.train.restrict
      (inducedACarrierToShared A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding))).castHeight_adjacentParameters
      (fun edge : OldACarrierEdge A Source.toRelStructure => edge.1)
      hLen
      (fun ρ =>
        Source.part ⁻¹'
          (fineAllowedFromRefinement
            (q :: tail).length R.extraCuts
            (by simp : 0 < (q :: tail).length)
            e.toFunctionEmbedding allowed R.permitted ρ))
      hFineParameters
  have hCuts : ∀ j : Fin lower.length, 0 < j.val →
      LabelledGirthGT
        (FineTrain.wagonClassCarrier
          (fun edge : OldACarrierEdge A Source.toRelStructure => edge.1)
          j.castSucc) (lower.get j) := by
    intro j hj
    let jOld : Fin ((q :: tail).length + R.extraCuts) :=
      Fin.cast hLen.symm j
    have hjOld : 0 < jOld.val := by
      change 0 < j.val
      exact hj
    have hOldIndex :
        (⟨jOld.val, by rw [← hLen]; exact jOld.isLt⟩ :
          Fin lower.length) = j := by
      apply Fin.ext
      rfl
    have hOldCut : LabelledGirthGT
        ((R.train.restrict
          (inducedACarrierToShared A stage.system.toRelStructure
            (activeCarrier A stage.system e.toFunctionEmbedding))).wagonClassCarrier
          (fun edge : OldACarrierEdge A Source.toRelStructure => edge.1)
          jOld.castSucc) (lower.get j) := by
      simpa only [hOldIndex, Source, lower] using
        hFineCuts jOld hjOld
    apply (R.train.restrict
      (inducedACarrierToShared A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding))).castHeight_labelledCutGirth
      (fun edge : OldACarrierEdge A Source.toRelStructure => edge.1)
      hLen j.castSucc (lower.get j)
    have hIndex :
        Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm
          j.castSucc = jOld.castSucc := by
      apply Fin.ext
      rfl
    rw [hIndex]
    exact hOldCut
  have hInitial := initialForestTailStage_of_partiteBaseTargetCuts
    A hA Source Large lowerFamily hFamilyParts
    lower htLower FineTrain allowedFine
    hSupport.1 hSupport.2.1 hGirth hParams hCuts
  exact ⟨hInitial⟩

end StructuralRamsey.Girth.TrainRecursiveWitness

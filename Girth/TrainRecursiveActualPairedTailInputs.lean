import Girth.TrainRecursiveActualRetainedSelectedWitnessGirth
import Girth.TrainRecursiveActualSelectedCoarseTrain
import Girth.TrainRecursiveCoarsenedGluingIdentity

set_option autoImplicit false
set_option Elab.async false

/-!
# One genuine selected lower stage supplies both old-level interfaces

This module combines two independent, exact physical bridges:
* full original positive-tail FullSystemGirthGT at each literal old cutoff;
* exact old/shared-train relation preservation and reflection at ALL cuts.

The lower stage uses exactly the prescribed first-wagon refinement, with
the replicated cutoff-vector height transported by equality. The two
conclusions refer to the SAME complete selected designated-copy subtype,
the SAME underlying relational gluing embeddings and the SAME forgotten
physical train. There is no extra hRel/hWitness premise, no carrier
quotient, pruning, and no invented lower recursive Ramsey stage.

This is a conditional interface, not a claim of a completed local
PictureStep or lower-stage existence.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P V X : Type v}

/-- A real refined selected lower stage provides both exact inputs
required at every positive original cut by the intrinsic Path A
attached-output theorem, and reflects EVERY original shared cut. -/
theorem ForestTailStage.coarsenedSelected_originalTailAndTrain_of_realRefinedStage
    (A : RelStructure L UA)
    (Old : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P)
    (Large : StructuralRamsey.Partite.System L UA V)
    {q : ℕ} {tail : List ℕ}
    (oldTrain : EdgeTrainLevels (OldACarrierEdge A Old.toRelStructure)
      (q :: tail).length)
    {edge : SharedOldACarrierEdge A Old.toRelStructure
      (activeCarrier A Old α) → Set X}
    {part : X → P} {firstAllowed : Set P} {g : ℕ}
    (R : FirstWagonRefinement
      (oldTrain.restrict (sharedOldACarrierInclusion A Old.toRelStructure
        (activeCarrier A Old α)))
      (by simp : 0 < (q :: tail).length)
      edge part firstAllowed g)
    {family : Set (Embedding
      (Old.toRelStructure.induce (activeCarrier A Old α))
      Large.toRelStructure)}
    {allowed : Fin ((List.replicate (R.extraCuts + 1) (q - 1) ++ tail).length + 1) → Set V}
    (S : ForestTailStage A
      (Old.toRelStructure.induce (activeCarrier A Old α))
      Large.toRelStructure family
      (List.replicate (R.extraCuts + 1) (q - 1) ++ tail)
      ((R.train.restrict (inducedACarrierToShared
        A Old.toRelStructure (activeCarrier A Old α))).castHeight
        (actualReplicatedCutoff_height_eq q R.extraCuts tail).symm)
      allowed)
    (hFamilyParts : ∀ b, b ∈ family →
      ∀ x : activeCarrier A Old α,
        Large.part (b x) = activeSourcePart A Old α x) :
    let E := S.system.coarsenVia Large S.isPartite
    let I := {b : DesignatedCopy
      (Old.toRelStructure.induce (activeCarrier A Old α))
      Large.toRelStructure S.system family // b ∈ S.selected}
    let f : I → Embedding
        (Old.toRelStructure.induce (activeCarrier A Old α))
        E.toRelStructure :=
      fun i => (selectedPartiteGluingFamily_of_largeBase
        (actualActiveSubsystemPartite A Old α)
        Large S.system S.isPartite family hFamilyParts
        S.selected i).toEmbedding
    let T := S.train.castHeight
      (actualReplicatedCutoff_height_eq q R.extraCuts tail)
    (∀ μ : Fin ((q :: tail).length + 1),
      ∀ i : I,
      ∀ p s : SharedOldACarrierEdge A Old.toRelStructure
        (activeCarrier A Old α),
        oldTrain.rel μ p.1 s.1 ↔
        (T.forgetFirstCuts (by simp : 0 < (q :: tail).length)).rel μ
          (sharedOldACarrierCoreEmbedding A Old.toRelStructure
            (activeCarrier A Old α) E.toRelStructure f i p)
          (sharedOldACarrierCoreEmbedding A Old.toRelStructure
            (activeCarrier A Old α) E.toRelStructure f i s)) ∧
    (∀ j : Fin (q :: tail).length, 0 < j.val →
      (sharedWitnessOrderOneData
        (T.forgetFirstCuts (by simp : 0 < (q :: tail).length))
        j.castSucc
        (sharedOldACarrierCoreEmbedding A Old.toRelStructure
          (activeCarrier A Old α) E.toRelStructure f)
        (Subtype.val : OldACarrierEdge A E.toRelStructure → Set S.Vertex)
      ).FullSystemGirthGT ((q :: tail).get j)) := by
  classical
  let E := S.system.coarsenVia Large S.isPartite
  let I := {b : DesignatedCopy
    (Old.toRelStructure.induce (activeCarrier A Old α))
    Large.toRelStructure S.system family // b ∈ S.selected}
  let f : I → Embedding
      (Old.toRelStructure.induce (activeCarrier A Old α))
      E.toRelStructure :=
    fun i => (selectedPartiteGluingFamily_of_largeBase
      (actualActiveSubsystemPartite A Old α)
      Large S.system S.isPartite family hFamilyParts
      S.selected i).toEmbedding
  let T := S.train.castHeight
    (actualReplicatedCutoff_height_eq q R.extraCuts tail)
  dsimp only
  constructor
  · intro μ i p s
    have hRel :=
      S.coarseSharedTrain_iff_of_realRefinedLower
        A Old.toRelStructure (activeCarrier A Old α)
        Large.toRelStructure oldTrain
        (by simp : 0 < (q :: tail).length)
        R (actualReplicatedCutoff_height_eq q R.extraCuts tail)
        allowed μ i p s
    exact hRel
  · exact S.coarsenedSelected_retainedSharedFullSystem_of_realStage
      A Old α Large hFamilyParts

end StructuralRamsey.Girth.TrainRecursiveWitness

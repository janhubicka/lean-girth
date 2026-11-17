import Girth.TrainCoverageFreePhysicalRefiningPass
import Girth.TrainCoverageFreePhysicalRefinedInput
import Girth.TrainCoverageFreePhysicalRefinementReady
import Girth.TrainCoverageFreePhysicalPositiveTransfer
import Girth.TrainPhysicalPartiteRefinedWitness
import Girth.TrainPhysicalPartiteProjectedForest
import Girth.TrainPhysicalRelationProjection

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nontrivial UA]
local notation "A" => A₀.ordered
local notation "hA" => RelStructure.HereditarilyIrreducible.irreducible
  (RelStructure.ordered_hereditarilyIrreducible A₀)
variable {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
variable {family : Set (Embedding B D)} {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}
local notation "Stage" => PhysicalForestStage A B D family (q :: tail) targetTrain allowed
local notation "m" => List.length (q :: tail)

/-- Build one actual higher-cutoff attachment from the forest assertion
at the strictly smaller vector of its maintained active refinement. -/
theorem refiningPictureStep_of_lowerForest
    (ht : Admissible (q :: tail)) (hq : 2 < q)
    (stage : Stage) (e : Embedding A D) (remaining : List (UA ↪ P))
    (hCovered : PhysicalForestStage.CoversBase stage)
    (hProject : stage.system.toRelStructure.IsHomomorphism D stage.system.part)
    (hFresh : e.toFunctionEmbedding ∉ remaining)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A stage.system
      e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val)
    (hReady : PhysicalForestStage.FirstRefinementReady (by simp) (q - 1)
      (e.toFunctionEmbedding :: remaining) stage)
    (hBaseLinear : ALinear A D)
    (hBaseStrong : ∀ b ∈ family, AStrong A D (copyCarrier b))
    (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
    (κ : Type w) [Nonempty κ]
    (hLower : ∀ d : ℕ, 0 < d → ProjectedFinePartiteForestAssertion A
      (List.replicate d (q - 1) ++ tail) κ) :
    ∃ next : Stage, PhysicalForestStage.FirstRefinementReady (by simp) (q - 1) remaining next ∧
      next.system.toRelStructure.IsHomomorphism D next.system.part ∧
      PictureStep stage next e.toFunctionEmbedding κ := by
  classical
  obtain ⟨R⟩ := hReady e.toFunctionEmbedding (List.mem_cons_self)
  obtain ⟨hFine, hSupport, hTwo, hParams, hGirth⟩ :=
    refinedActiveInput A₀ stage e R ht hq hPair
  let Target := actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding
  have hActiveProject := activeFine_isHomomorphism_of_partProjection A D stage.system e hProject
  obtain ⟨W, hCoreProject⟩ := hLower (R.extraCuts + 1) (Nat.succ_pos _)
    Target (refinedActiveTrain stage e R) (refinedActiveAllowed stage e R)
    hActiveProject hFine hSupport hTwo hParams hGirth
  letI : Finite W.Vertex := W.finiteVertex
  letI : Finite W.Index := W.finiteIndex
  obtain ⟨a, b, hab⟩ := hPair
  let E := W.core.relabel e.toFunctionEmbedding
  let f := fun i : W.Index => activePartiteToRelabelledCore
    A stage.system e.toFunctionEmbedding W.core (W.selected i)
  let U := EdgeTrainLevels.forgetFirstCuts
    (W.train.castHeight (actualReplicatedCutoff_height_eq q R.extraCuts tail)) (by simp : 0 < m)
  have hRigid : ∀ a : Embedding A D, SameCopy a e → a = e :=
    fun a h => ordered_embedding_eq_of_sameCopy a e h
  have hSelectedStrong (b : DesignatedCopy B D stage.system family) (_ : b ∈ stage.selected) :
      AStrong A D (copyCarrier b.base) := hBaseStrong b.base b.base_mem
  have hCoarse := W.refinedCoarseTrain A stage.system e.toFunctionEmbedding stage.train allowed R
  have hInterior := fun (μ : Fin (m + 1)) (_ : 0 < μ.val) (_ : μ.val < m) i p r => hCoarse.1 μ i p r
  have hPositive := fun j hj => W.refinedRetainedFull
    A stage.system e.toFunctionEmbedding stage.train allowed R j hj
  have hCutoff (j : Fin m) : 2 ≤ (q :: tail).get j := ht.two_le _ (List.get_mem _ _)
  have hFullOut := PhysicalForestStage.actual_positive_full_of_Ft stage hA hBaseLinear
    e hRigid a E f U hCovered hSelectedStrong hTargetTwo hCutoff hInterior hPositive
  let bounds : ActiveAttachmentBounds stage hA e a E f U := by
    refine {
      coreProjectsACopies := projectsACopies_relabel_of_fineEdges A D W.core e W.fineEdges
      coreSupportNonempty := W.supportNonempty
      coreSupportCovers := W.supportCovers
      baseStrong := hSelectedStrong
      targetTwo := hTargetTwo
      interior := hInterior
      bottomTwo := by simp; omega
      localForest := Or.inr ⟨?_, W.selectedSupports,
        W.refinedMixedForest A stage.system e.toFunctionEmbedding stage.train allowed R⟩
      coreGirth := fun _ => W.refinedCoreGirth A stage.system e.toFunctionEmbedding
        stage.train allowed R hA hq ht.nondecreasing
      cutoffTwo := by intro h; simp at h; omega
      coreParameters := hCoarse.2
      interiorFull := ?_
      tailSupreme := fun j hj => (hFullOut j hj).2
    }
    · obtain ⟨r, s, hrs⟩ := activeSupport_two_distinct_of_projected_carriers
        A stage.system e.toFunctionEmbedding a b hab
      exact ⟨r.val, s.val, r.property, s.property, fun h => hrs (Subtype.ext h)⟩
    · intro μ hPos hLt
      let j : Fin m := ⟨μ.val, hLt⟩
      have hIndex : j.castSucc = μ := Fin.ext rfl
      have h := hPositive j hPos
      rw [hIndex] at h
      refine ⟨h.1, ?_⟩
      intro n C hAccept hOrder
      exact h.2 n C hAccept (Nat.le_trans hOrder (Nat.mul_le_mul_left 2 (hCutoff j)))
  let next := PhysicalForestStage.activeAttachment_of_bounds stage hA hBaseLinear
    e hRigid a E f U bounds
  have hKeep : PhysicalForestStage.FirstRefinementReady (by simp) (q - 1)
      remaining next := by
    exact PhysicalForestStage.activeAttachment_firstRefinementReady A₀ stage hBaseLinear
      e a E f U bounds (fun y => ⟨W.core.part y, rfl⟩) (by simp) remaining hFresh hReady
  have hNextProject : next.system.toRelStructure.IsHomomorphism D next.system.part :=
    StructuralRamsey.Partite.Attachment.isHomomorphism_of_partProjections stage.system
      (activeCarrier A stage.system e.toFunctionEmbedding) E f D hProject
      (StructuralRamsey.Partite.System.isHomomorphism_relabel_of_partProjection W.core A D e hCoreProject)
  refine ⟨next, hKeep, hNextProject, PhysicalForestStage.activeAttachment_pictureStep_of_familyArrow
    stage hA hBaseLinear e hRigid a E f U bounds κ ?_⟩
  intro χ
  let ψ : OldACarrierEdge A W.core.toRelStructure → κ := fun edge =>
    χ (Classical.choose edge.property)
  obtain ⟨i, hi⟩ := W.physicalArrow ψ
  refine ⟨i, fun a b => ?_⟩
  have hColour (d : Embedding A W.core.toRelStructure) : ψ (actualEdge d) = χ d := by
    dsimp only [ψ]
    congr 1
    exact ordered_embedding_eq_of_sameCopy _ d
      (Classical.choose_spec (actualEdge d).property).symm
  change χ ((W.selected i).toEmbedding.comp a) = χ ((W.selected i).toEmbedding.comp b)
  simpa only [hColour] using hi a b

/-- The complete higher-cutoff physical pass over a supplied linear
Ramsey base, using only the lower forest assertions. -/
theorem ramseyForest_largerCutoff [Nonempty UA] [Finite VB] [Finite P]
    (ht : Admissible (q :: tail)) (hq : 2 < q)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ b : VB, ∃ e : OldACarrierEdge A B, b ∈ e.1)
    (hTargetParameters : ∀ b : family, targetTrain.AdjacentParameters
      (fun edge => edge.1) (fun ν => b.val ⁻¹' allowed ν))
    (hTargetCuts : ∀ j : Fin m, LabelledGirthGT
      (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc) ((q :: tail).get j))
    (hBaseLinear : ALinear A D)
    (hBaseStrong : ∀ b ∈ family, AStrong A D (copyCarrier b))
    (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
    (κ : Type w) [Nonempty κ]
    (hBase : ∀ χ : Embedding A D → κ, ∃ b, b ∈ family ∧
      ∀ a₁ a₂ : Embedding A B, χ (b.comp a₁) = χ (b.comp a₂))
    (hLower : ∀ d : ℕ, 0 < d → ProjectedFinePartiteForestAssertion A
      (List.replicate d (q - 1) ++ tail) κ) :
    ∃ next : Stage, next.system.toRelStructure.IsHomomorphism D next.system.part ∧
      DesignatedArrow next κ := by
  have hGirth := ordinaryGirth_of_targetBottomLabelledCut A B targetTrain q
    (hTargetCuts ⟨0, by simp⟩)
  apply ramseyForest_fromTargetCuts_of_freshPhysicalRefiningSteps A₀ ht hSupportNonempty
    hSupportCovers hGirth hTargetParameters (fun j _ => hTargetCuts j) (q - 1) κ hBase
  intro e remaining stage hCovered hProject hFresh hPair hReady
  exact refiningPictureStep_of_lowerForest A₀ ht hq stage e remaining hCovered hProject hFresh
    hPair hReady hBaseLinear hBaseStrong hTargetTwo κ hLower

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

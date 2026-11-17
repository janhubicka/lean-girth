import Girth.TrainCoverageFreePhysicalDirectPartiteFtStep
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# RAW physical F_t witness with fine edge parts, not ordered IsPartiteOver

This record contains exactly the type of local F_t data used by the
physical selected attachment: the true active source, a finite witness
of the same one-edge coloured type, one selected embedding per
physical support image, the same-q mixed finite SET forests, exact
train restrictions, positive full-system bounds, parameters, and
indexed PHYSICAL A-edge colouring arrow.

Crucially, its fineEdges field states only that every physical
A-embedding uses the prescribed fine A-part labels. It does NOT
postulate IsPartiteOver of the full order-expanded ambient structure,
mixedCoverage, output girth or an already-constructed PictureStep.
A separate theorem constructs the PictureStep using the source-level
weak physical stage attachment. The abstract F_t existence assertion
is not formally constructed here. UNCOMPILED SOURCE.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable (A₀ : RelStructure L UA)
variable [LinearOrder UA] [Finite UA] [Nontrivial UA]
local notation "A" => A₀.ordered

variable {B : RelStructure L.withOrder VB}
variable {D : RelStructure L.withOrder P}
variable {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels
  (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

/-- Precisely the local forest-witness data on the TRUE induced
A-partite source. It does not assume a previous recursive stage
or the resulting picture step. -/
structure RawPartiteFtWitness
    (stage : PhysicalForestStage A B D family (q :: tail) targetTrain allowed)
    (e : Embedding A D) (κ : Type w) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  Index : Type v
  finiteIndex : Finite Index
  core : StructuralRamsey.Partite.System L.withOrder UA Vertex
  selected : Index → StructuralRamsey.Partite.Embedding
    (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding) core
  train : EdgeTrainLevels
    (OldACarrierEdge A core.toRelStructure) (q :: tail).length
  fineEdges : ∀ a : Embedding A core.toRelStructure,
    ∀ x : UA, core.part (a x) = x
  supportNonempty : Nonempty (OldACarrierEdge A core.toRelStructure)
  supportCovers : ∀ y : Vertex,
    ∃ edge : OldACarrierEdge A core.toRelStructure, y ∈ edge.1
  selectedSupports : Function.Injective
    (fun i : Index => bSupportPiece A ((selected i).toEmbedding))
  mixedForest : FiniteMixedForestThrough
    (RelationalMixedSupportTest A
      (fun i : Index => (selected i).toEmbedding)) q
  selectedTrain :
    ∀ (μ : Fin ((q :: tail).length + 1)) (i : Index)
      (a b : Embedding A
        (actualActiveSubsystemPartite A stage.system
          e.toFunctionEmbedding).toRelStructure),
      train.rel μ
        (actualEdge ((selected i).toEmbedding.comp a))
        (actualEdge ((selected i).toEmbedding.comp b)) ↔
      (((stage.train.restrict
        (sharedOldACarrierInclusion A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding))).restrict
        (inducedACarrierToShared A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding))).rel μ)
            (actualEdge a) (actualEdge b)
  fineParameters : train.AdjacentParameters
    (fun edge => edge.1)
    (fun ν => core.part ⁻¹' (e.toFunctionEmbedding ⁻¹' allowed ν))
  positiveFull :
    ∀ j : Fin (q :: tail).length, 0 < j.val →
      (activeGluingWitnessOrderOneData A stage.system
        e.toFunctionEmbedding core.toRelStructure
        (fun i : Index => (selected i).toEmbedding) train j.castSucc)
        .FullSystemGirthGT ((q :: tail).get j)
  physicalArrow :
    ∀ χ : OldACarrierEdge A core.toRelStructure → κ,
      ∃ i : Index,
        ∀ a b : Embedding A
          (actualActiveSubsystemPartite A stage.system
            e.toFunctionEmbedding).toRelStructure,
          χ (actualEdge ((selected i).toEmbedding.comp a)) =
            χ (actualEdge ((selected i).toEmbedding.comp b))

/-- A genuine RAW local F_t witness produces the full next selected
PhysicalOrderStage and PictureStep, by the direct physical construction.
Unlike a supplied local picture-step operator, this record contains
no assertion about the output of the construction. -/
theorem RawPartiteFtWitness.toPictureStep
    (stage : PhysicalForestStage A B D family (q :: tail) targetTrain allowed)
    (e : Embedding A D) (κ : Type w) [Nonempty κ]
    (W : RawPartiteFtWitness A₀ stage e κ)
    (hBaseLinear : ALinear A D)
    (hReady : stage.Ready)
    (hSelectedStrong :
      ∀ b : DesignatedCopy B D stage.system family,
        b ∈ stage.selected → AStrong A D (copyCarrier b.base))
    (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
    (hCutoff : ∀ j : Fin (q :: tail).length,
      2 ≤ (q :: tail).get j)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val) :
    ∃ next : PhysicalOrderStage A B D family (q :: tail) targetTrain allowed,
      PictureStep stage next.toPhysicalForestStage
        e.toFunctionEmbedding κ := by
  letI : Finite W.Vertex := W.finiteVertex
  letI : Finite W.Index := W.finiteIndex
  classical
  let active : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding := Classical.choose hPair
  exact stage.orderPictureStep_of_rawPartiteFt A₀ hBaseLinear
    e active W.core W.selected W.train
    hReady.1 hReady.2 hSelectedStrong hTargetTwo hCutoff
    hPair W.fineEdges W.supportNonempty W.supportCovers
    W.selectedSupports W.mixedForest W.selectedTrain
    W.fineParameters W.positiveFull κ W.physicalArrow

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

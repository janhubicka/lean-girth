import Girth.TrainCoverageFreeDirectPartiteFtStep
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Raw standalone forest-witness interface, not a picture-step oracle

This packages a candidate local output of the circulation forest assertion
with one EXTRA property: IsPartiteOver for the full order-expanded
language. That is not automatic from F_t at q=2. The actual raw
F_t output only has the prescribed coloured-edge type on the
unordered reduct plus auxiliary part orders.

The intended weaker replacement will separate those auxiliary orders
from the relational partite projection. Until that is formalized,
this structure is a STRONGER CONDITIONAL interface, not a faithful
formalization of F_t.

The remaining fields package the other expected local data:
a finite train, one-per-image selected embeddings, the mixed finite
SET forest, exact train reflection, fine-part parameters, positive
FULL system bounds and the PHYSICAL edge-colouring arrow.
They do not repair the additional ordered IsPartiteOver premise. The support properties
belong to the definition of a train.

The record does NOT include mixedCoverage, an old-picture girth
certificate, an output picture stage, or any requested output
Ramsey/girth conclusion. A separate theorem constructs the latter
using the genuine coverage-free physical attachment.

The conversion from the abstract English F_t assertion to existence
of this record still requires formalizing the coloured-edge train
assertion. This module is source-only and UNCOMPILED.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

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
    (stage : ForestStage A B D family (q :: tail) targetTrain allowed)
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
  partite : core.IsPartiteOver A
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
OrderStage and PictureStep, by the direct physical construction.
Unlike a supplied local picture-step operator, this record contains
no assertion about the output of the construction. -/
theorem RawPartiteFtWitness.toPictureStep
    (stage : ForestStage A B D family (q :: tail) targetTrain allowed)
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
    ∃ next : OrderStage A B D family (q :: tail) targetTrain allowed,
      PictureStep stage next.toForestStage
        e.toFunctionEmbedding κ := by
  letI : Finite W.Vertex := W.finiteVertex
  letI : Finite W.Index := W.finiteIndex
  classical
  let active : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding := Classical.choose hPair
  exact stage.orderPictureStep_of_rawPartiteFt A₀ hBaseLinear
    e active W.core W.selected W.train
    hReady.1 hReady.2 hSelectedStrong hTargetTwo hCutoff
    hPair W.partite W.supportNonempty W.supportCovers
    W.selectedSupports W.mixedForest W.selectedTrain
    W.fineParameters W.positiveFull κ W.physicalArrow

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

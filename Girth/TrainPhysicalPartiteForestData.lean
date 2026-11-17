import Girth.ForestActualRecursiveSupport
import Girth.LabelledWagonCutRestriction
import Girth.TrainAdjacentParameters
import Girth.TrainRecursiveWitnessPass
import Girth.TrainSimultaneousSupreme

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA X : Type v}

/-- The train system of the selected whole images in a fine-partite
witness. It uses all physical A-edges, including unselected ones. -/
def finePartiteWitnessOrderOneData
    (A : RelStructure L UA) {Y I : Type v}
    {Target : RelStructure L X} {Core : RelStructure L Y}
    (f : I → Embedding Target Core)
    {m : ℕ} (U : EdgeTrainLevels (OldACarrierEdge A Core) m)
    (μ : Fin (m + 1)) :
    OrderOneData Y (OldACarrierEdge A Core) I (Quotient (U.wagonSetoid μ)) where
  edgeCarrier := fun edge => edge.1
  copyCarrier := fun i => copyCarrier (f i)
  copyEdges := fun i => {edge | edge.1 ⊆ copyCarrier (f i)}
  parent := Quotient.mk (U.wagonSetoid μ)

/-- Fine-partite forest data expressed entirely in terms of the target train. -/
structure FinePartiteFtWitness
    (A : RelStructure L UA) (Target : StructuralRamsey.Partite.System L UA X)
    (t : List ℕ) (sourceTrain : EdgeTrainLevels (OldACarrierEdge A Target.toRelStructure) t.length)
    (allowedFine : Fin (t.length + 1) → Set UA) (κ : Type w) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  Index : Type v
  finiteIndex : Finite Index
  core : StructuralRamsey.Partite.System L UA Vertex
  selected : Index → StructuralRamsey.Partite.Embedding Target core
  train : EdgeTrainLevels (OldACarrierEdge A core.toRelStructure) t.length
  fineEdges : ∀ a : Embedding A core.toRelStructure, ∀ x : UA, core.part (a x) = x
  supportNonempty : Nonempty (OldACarrierEdge A core.toRelStructure)
  supportCovers : ∀ y : Vertex, ∃ edge : OldACarrierEdge A core.toRelStructure, y ∈ edge.1
  selectedSupports : Function.Injective (fun i : Index => bSupportPiece A (selected i).toEmbedding)
  mixedForest : FiniteMixedForestThrough
    (RelationalMixedSupportTest A (fun i : Index => (selected i).toEmbedding)) (t.headD 0)
  selectedTrain : ∀ (μ : Fin (t.length + 1)) (i : Index)
      (a b : Embedding A Target.toRelStructure),
    train.rel μ (actualEdge ((selected i).toEmbedding.comp a))
      (actualEdge ((selected i).toEmbedding.comp b)) ↔
    sourceTrain.rel μ (actualEdge a) (actualEdge b)
  fineParameters : train.AdjacentParameters (fun edge => edge.1)
    (fun ν => core.part ⁻¹' allowedFine ν)
  positiveFull : ∀ j : Fin t.length, 0 < j.val →
    (finePartiteWitnessOrderOneData A (fun i : Index => (selected i).toEmbedding)
      train j.castSucc).FullSystemGirthGT (t.get j)
  physicalArrow : ∀ χ : OldACarrierEdge A core.toRelStructure → κ,
    ∃ i : Index, ∀ a b : Embedding A Target.toRelStructure,
      χ (actualEdge ((selected i).toEmbedding.comp a)) =
      χ (actualEdge ((selected i).toEmbedding.comp b))

/-- The standalone local forest assertion consumed by the finite pass. The
input consists of a fine-partite target with physical support at every
vertex, together with its train, parameters and labelled wagon girth. -/
def FinePartiteForestAssertion (A : RelStructure L UA) (t : List ℕ) (κ : Type w) : Prop :=
  ∀ {X : Type v} [Finite X] (Target : StructuralRamsey.Partite.System L UA X)
    (sourceTrain : EdgeTrainLevels (OldACarrierEdge A Target.toRelStructure) t.length)
    (allowedFine : Fin (t.length + 1) → Set UA),
    (∀ a : Embedding A Target.toRelStructure, ∀ u : UA, Target.part (a u) = u) →
    (∀ x : X, ∃ a : Embedding A Target.toRelStructure, x ∈ copyCarrier a) →
    (∃ a b : Embedding A Target.toRelStructure, ¬ SameCopy a b) →
    sourceTrain.AdjacentParameters (fun edge => edge.1)
      (fun ν => Target.part ⁻¹' allowedFine ν) →
    (∀ j : Fin t.length,
      LabelledGirthGT (sourceTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        (t.get j)) →
    Nonempty (FinePartiteFtWitness A Target t sourceTrain allowedFine κ)

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

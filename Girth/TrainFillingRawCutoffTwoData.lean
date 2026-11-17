import Girth.TrainFillingRelationalLabelTransport
import Girth.ForestActualRecursiveSupport
import Girth.TrainRecursiveWitnessPass

set_option autoImplicit false

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v w
variable {L : RelLanguage.{u}} {A V Y I : Type v}

/-- The actual local witness before the cutoff-two increment. Its
predecessor forest is through one. The increment is responsible for
the forest at the new bottom cutoff. -/
structure CutoffTwoRawLocalData
    (small : RelStructure L A) (Target : System L A V) (tail : List ℕ)
    (original : EdgeTrainLevels (OldACarrierEdge small Target.toRelStructure) (tail.length + 1))
    (allowed : Fin (tail.length + 1 + 1) → Set A) (κ : Type w) where
  system : System L A Y
  selected : I → StructuralRamsey.Partite.Embedding Target system
  train : EdgeTrainLevels (OldACarrierEdge small system.toRelStructure) (tail.length + 1)
  projection : system.toRelStructure.IsHomomorphism small system.part
  supportNonempty : Nonempty (OldACarrierEdge small system.toRelStructure)
  supportCovers : ∀ y : Y, ∃ e : OldACarrierEdge small system.toRelStructure, y ∈ e.1
  fineEdges : ∀ a : Embedding small system.toRelStructure, ∀ x : A, system.part (a x) = x
  aLinear : ALinear small system.toRelStructure
  strong : ∀ i : I, AStrong small system.toRelStructure (copyCarrier (selected i).toEmbedding)
  predecessor : FiniteMixedForestThrough
    (RelationalMixedSupportTest small (fun i => (selected i).toEmbedding)) 1
  selectedTrain : ∀ μ (i : I) (a b : Embedding small Target.toRelStructure),
    train.rel μ (actualEdge ((selected i).toEmbedding.comp a))
      (actualEdge ((selected i).toEmbedding.comp b)) ↔
      original.rel μ (actualEdge a) (actualEdge b)
  parameters : train.AdjacentParameters Subtype.val (fun ν => system.part ⁻¹' allowed ν)
  positive : ∀ j : Fin tail.length,
    (train.carrierCutData (fun i => copyCarrier (selected i).toEmbedding)
      j.castSucc.succ).FullSystemGirthGT (tail.get j)
  arrow : ∀ χ : OldACarrierEdge small system.toRelStructure → κ,
    ∃ i : I, ∀ a b : Embedding small Target.toRelStructure,
      χ (actualEdge ((selected i).toEmbedding.comp a)) =
        χ (actualEdge ((selected i).toEmbedding.comp b))

end StructuralRamsey.Girth.TrainRecursiveWitness

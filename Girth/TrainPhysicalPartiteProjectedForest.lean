import Girth.TrainPhysicalPartiteForestData

set_option autoImplicit false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA : Type v}

/-- The forest assertion for targets whose fine-part map preserves the
relations of the edge type. The output retains this projection. -/
def ProjectedFinePartiteForestAssertion (A : RelStructure L UA) (t : List ℕ) (κ : Type w) : Prop :=
  ∀ {X : Type v} [Finite X] (Target : StructuralRamsey.Partite.System L UA X)
    (sourceTrain : EdgeTrainLevels (OldACarrierEdge A Target.toRelStructure) t.length)
    (allowedFine : Fin (t.length + 1) → Set UA),
    Target.toRelStructure.IsHomomorphism A Target.part →
    (∀ a : Embedding A Target.toRelStructure, ∀ u : UA, Target.part (a u) = u) →
    (∀ x : X, ∃ a : Embedding A Target.toRelStructure, x ∈ copyCarrier a) →
    (∃ a b : Embedding A Target.toRelStructure, ¬ SameCopy a b) →
    sourceTrain.AdjacentParameters (fun edge => edge.1)
      (fun ν => Target.part ⁻¹' allowedFine ν) →
    (∀ j : Fin t.length,
      LabelledGirthGT (sourceTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        (t.get j)) →
    ∃ W : FinePartiteFtWitness A Target t sourceTrain allowedFine κ,
      W.core.toRelStructure.IsHomomorphism A W.core.part

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

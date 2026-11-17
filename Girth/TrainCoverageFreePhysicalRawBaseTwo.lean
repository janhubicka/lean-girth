import Girth.TrainCoverageFreePhysicalFineForestAssertion
import Girth.TrainPhysicalPartiteForestBaseTwo

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- A projected active A-copy supplies the nonempty support of the genuine
cutoff-two witness on its physical fibre. -/
theorem PhysicalForestStage.rawPartiteFtWitness_baseTwo
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nontrivial UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) 1}
    {allowed : Fin 2 → Set P}
    (stage : PhysicalForestStage A₀.ordered B D family [2] targetTrain allowed)
    (e : Embedding A₀.ordered D)
    (active : StructuralRamsey.Partite.ProjectedEmbedding A₀.ordered
      stage.system e.toFunctionEmbedding)
    (hSpan : ∃ (R : L.Symbol) (z : Fin (L.arity R) → UA),
      A₀.rel R z ∧ Function.Surjective z)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    Nonempty (RawPartiteFtWitness A₀ stage e κ) := by
  let A := A₀.ordered
  let α := e.toFunctionEmbedding
  let S := activeCarrier A stage.system α
  let Target := actualActiveSubsystemPartite A stage.system α
  let activeInduced : Embedding A Target.toRelStructure :=
    (activeInduceProjected A active (projected_mem_activeCarrier A stage.system α active)).val
  have hFine (a : Embedding A Target.toRelStructure) (u : UA) : Target.part (a u) = u :=
    actualActiveSubsystemPartite_fineEdges_of_projectedACopies A D stage.system
      stage.projectsACopies e (fun b h => ordered_embedding_eq_of_sameCopy b e h) a u
  have hSupport (x : S) : ∃ a : Embedding A Target.toRelStructure, x ∈ copyCarrier a := by
    obtain ⟨edge, ⟨a, rfl⟩, hx⟩ := actualRecursiveActiveSupport_cover A stage.system α x
    exact ⟨a, hx⟩
  exact finePartiteFtWitness_baseTwo_of_spanningTuple A₀ Target (stage.activeFineTrain e)
    (fun ν => α ⁻¹' allowed ν) activeInduced hSpan hFine (aLinear_induce stage.aLinear S)
    hSupport (PhysicalForestStage.trueActive_fineParameters stage e) κ

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

#print axioms StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical.PhysicalForestStage.rawPartiteFtWitness_baseTwo

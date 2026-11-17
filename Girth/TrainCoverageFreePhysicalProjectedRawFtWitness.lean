import Girth.TrainCoverageFreePhysicalFineForestAssertion
import Girth.TrainPhysicalPartiteProjectedForest
import Girth.TrainPhysicalRelationProjection

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- Apply the projected forest assertion to the true active subsystem,
retaining the inherited train, allowed parts and actual local core projection. -/
theorem PhysicalForestStage.rawPartiteFtWitness_of_projectedFinePartiteForestAssertion
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nontrivial UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)} {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (stage : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed)
    (e : Embedding A₀.ordered D) (κ : Type w)
    (hProject : stage.system.toRelStructure.IsHomomorphism D stage.system.part)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered stage.system e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val)
    (hWagonGirth : PhysicalForestStage.ActiveWagonGirth A₀ stage e)
    (hForest : ProjectedFinePartiteForestAssertion A₀.ordered (q :: tail) κ) :
    ∃ W : RawPartiteFtWitness A₀ stage e κ,
      W.core.toRelStructure.IsHomomorphism A₀.ordered W.core.part := by
  let A := A₀.ordered
  let α := e.toFunctionEmbedding
  let S := activeCarrier A stage.system α
  let Target := actualActiveSubsystemPartite A stage.system α
  have hTargetProject : Target.toRelStructure.IsHomomorphism A Target.part :=
    activeFine_isHomomorphism_of_partProjection A D stage.system e hProject
  have hFine (a : Embedding A Target.toRelStructure) (x : UA) : Target.part (a x) = x :=
    actualActiveSubsystemPartite_fineEdges_of_projectedACopies A D stage.system
      stage.projectsACopies e (fun b h => ordered_embedding_eq_of_sameCopy b e h) a x
  have hSupport (x : S) : ∃ a : Embedding A Target.toRelStructure, x ∈ copyCarrier a := by
    obtain ⟨edge, ⟨a, rfl⟩, hx⟩ := actualRecursiveActiveSupport_cover A stage.system α x
    exact ⟨a, hx⟩
  have hTwo := activeTarget_twoGenuineCopies_of_nontrivialFibre A stage.system α hPair
  exact hForest Target (stage.activeFineTrain e) (fun ν => α ⁻¹' allowed ν)
    hTargetProject hFine hSupport hTwo
    (PhysicalForestStage.trueActive_fineParameters stage e) hWagonGirth

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

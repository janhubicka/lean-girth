import Girth.TrainCoverageFreePhysicalRawFtData
import Girth.TrainRecursiveParameterRestrictionKernel
import Girth.TrainRecursiveTrueActiveAdjacentParameters
import Girth.TrainRecursiveTrueActiveTwoCopies

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The true active train inherits the complete adjacent parameters in its
fine part coordinates. The allowed parts are the preimages under `e`. -/
theorem PhysicalForestStage.trueActive_fineParameters
    {A : RelStructure L UA} {B : RelStructure L VB} {D : RelStructure L P}
    {family : Set (Embedding B D)} {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (stage : PhysicalForestStage A B D family t targetTrain allowed)
    (e : Embedding A D) :
    let Target := actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding
    (stage.activeFineTrain e).AdjacentParameters
      (fun edge : OldACarrierEdge A Target.toRelStructure => edge.1)
      (fun ν => Target.part ⁻¹' (e.toFunctionEmbedding ⁻¹' allowed ν)) := by
  let α := e.toFunctionEmbedding
  let S := activeCarrier A stage.system α
  let Target := actualActiveSubsystemPartite A stage.system α
  let keepOld := sharedOldACarrierInclusion A stage.system.toRelStructure S
  let keepFine := inducedACarrierToShared A stage.system.toRelStructure S
  let shared := stage.train.restrict keepOld
  let inclusion : S ↪ stage.Vertex := ⟨Subtype.val, Subtype.val_injective⟩
  have hShared : shared.AdjacentParameters
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S => edge.1.1)
      (fun ν => stage.system.part ⁻¹' allowed ν) :=
    stage.train.adjacentParameters_restrict
      (fun edge : OldACarrierEdge A stage.system.toRelStructure => edge.1)
      keepOld (fun edge => edge.1.1) (fun _ => Set.Subset.rfl)
      (fun ν => stage.system.part ⁻¹' allowed ν) stage.parameters
  have hCarrier (edge : OldACarrierEdge A Target.toRelStructure) (x : S) (hx : x ∈ edge.1) :
      x.val ∈ (keepFine edge).1.1 :=
    ⟨x, hx, rfl⟩
  have hAllow (ν : Fin (t.length + 1)) (x : S)
      (hx : stage.system.part x.val ∈ allowed ν) :
      Target.part x ∈ α ⁻¹' allowed ν := by
    change α (activeSourcePart A stage.system α x) ∈ allowed ν
    exact Eq.mpr (congrArg (fun p : P => p ∈ allowed ν)
      (activeSourcePart_spec A stage.system α x)) hx
  change (shared.restrict keepFine).AdjacentParameters
    (fun edge : OldACarrierEdge A Target.toRelStructure => edge.1)
    (fun ν => Target.part ⁻¹' (α ⁻¹' allowed ν))
  exact shared.adjacentParameters_restrict_of_vertexEmbedding
    (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S => edge.1.1)
    keepFine inclusion (fun edge : OldACarrierEdge A Target.toRelStructure => edge.1)
    hCarrier (fun ν => stage.system.part ⁻¹' allowed ν)
    (fun ν => Target.part ⁻¹' (α ⁻¹' allowed ν)) hAllow hShared

/-- The actual recursive target meets the standalone forest assertion's
inputs whenever its projected fibre is nontrivial and has the inherited
same-vector wagon girth. -/
theorem PhysicalForestStage.rawPartiteFtWitness_of_finePartiteForestAssertion
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nontrivial UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)} {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (stage : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed)
    (e : Embedding A₀.ordered D) (κ : Type w)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered stage.system e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val)
    (hWagonGirth : PhysicalForestStage.ActiveWagonGirth A₀ stage e)
    (hForest : FinePartiteForestAssertion A₀.ordered (q :: tail) κ) :
    Nonempty (RawPartiteFtWitness A₀ stage e κ) := by
  let A := A₀.ordered
  let α := e.toFunctionEmbedding
  let S := activeCarrier A stage.system α
  let Target := actualActiveSubsystemPartite A stage.system α
  have hFine (a : Embedding A Target.toRelStructure) (x : UA) : Target.part (a x) = x :=
    actualActiveSubsystemPartite_fineEdges_of_projectedACopies A D stage.system
      stage.projectsACopies e (fun b h => ordered_embedding_eq_of_sameCopy b e h) a x
  have hSupport (x : S) : ∃ a : Embedding A Target.toRelStructure, x ∈ copyCarrier a := by
    obtain ⟨edge, ⟨a, rfl⟩, hx⟩ := actualRecursiveActiveSupport_cover A stage.system α x
    exact ⟨a, hx⟩
  have hTwo := activeTarget_twoGenuineCopies_of_nontrivialFibre A stage.system α hPair
  exact hForest Target (stage.activeFineTrain e) (fun ν => α ⁻¹' allowed ν) hFine hSupport hTwo
    (PhysicalForestStage.trueActive_fineParameters stage e) hWagonGirth

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

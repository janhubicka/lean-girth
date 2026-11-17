import Girth.TrainCoverageFreePhysicalDirectPartiteFtStep
import Girth.TrainCoverageFreePhysicalRawFtData
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- A genuine RAW local F_t witness produces the full next selected
PhysicalOrderStage and PictureStep, by the direct physical construction.
Unlike a supplied local picture-step operator, this record contains
no assertion about the output of the construction. -/
theorem RawPartiteFtWitness.toPictureStep
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nontrivial UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)} {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (stage : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed)
    (e : Embedding A₀.ordered D) (κ : Type w) [Nonempty κ]
    (W : RawPartiteFtWitness A₀ stage e κ)
    (hBaseLinear : ALinear A₀.ordered D)
    (hReady : stage.Ready)
    (hSelectedStrong :
      ∀ b : DesignatedCopy B D stage.system family,
        b ∈ stage.selected → AStrong A₀.ordered D (copyCarrier b.base))
    (hTargetTwo : ∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b)
    (hCutoff : ∀ j : Fin (q :: tail).length,
      2 ≤ (q :: tail).get j)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered stage.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val) :
    ∃ next : PhysicalOrderStage A₀.ordered B D family (q :: tail) targetTrain allowed,
      PictureStep stage next.toPhysicalForestStage
        e.toFunctionEmbedding κ := by
  letI : Finite W.Vertex := W.finiteVertex
  letI : Finite W.Index := W.finiteIndex
  classical
  let active : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered stage.system e.toFunctionEmbedding := Classical.choose hPair
  exact PhysicalForestStage.orderPictureStep_of_rawPartiteFt A₀ stage hBaseLinear
    e active W.core W.selected W.train
    hReady.1 hReady.2 hSelectedStrong hTargetTwo hCutoff
    hPair W.fineEdges W.supportNonempty W.supportCovers
    W.selectedSupports W.mixedForest W.selectedTrain
    W.fineParameters W.positiveFull κ W.physicalArrow

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

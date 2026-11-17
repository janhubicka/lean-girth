import Girth.TrainCoverageFreePhysicalRawFtWitness
import Girth.TrainPhysicalRelationProjection

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The same-vector physical step retains projection of every relation
tuple when the old picture and the fine raw witness both project. The
order-stage result is the actual free attachment. -/
theorem RawPartiteFtWitness.toProjectedPictureStep
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nontrivial UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)} {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (stage : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed)
    (e : Embedding A₀.ordered D) (κ : Type w) [Nonempty κ]
    (W : RawPartiteFtWitness A₀ stage e κ)
    (hProject : stage.system.toRelStructure.IsHomomorphism D stage.system.part)
    (hCoreProject : W.core.toRelStructure.IsHomomorphism A₀.ordered W.core.part)
    (hBaseLinear : ALinear A₀.ordered D)
    (hReady : PhysicalForestStage.Ready stage)
    (hSelectedStrong : ∀ b : DesignatedCopy B D stage.system family,
      b ∈ stage.selected → AStrong A₀.ordered D (copyCarrier b.base))
    (hTargetTwo : ∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b)
    (hCutoff : ∀ j : Fin (q :: tail).length, 2 ≤ (q :: tail).get j)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered stage.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val) :
    ∃ next : PhysicalOrderStage A₀.ordered B D family (q :: tail) targetTrain allowed,
      next.system.toRelStructure.IsHomomorphism D next.system.part ∧
      PictureStep stage next.toPhysicalForestStage e.toFunctionEmbedding κ := by
  classical
  let : Finite W.Vertex := W.finiteVertex
  let : Finite W.Index := W.finiteIndex
  let A := A₀.ordered
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  let E := W.core.relabel e.toFunctionEmbedding
  let f (i : W.Index) := activePartiteToRelabelledCore
    A stage.system e.toFunctionEmbedding W.core (W.selected i)
  let RF (i : W.Index) := (f i).toEmbedding
  let active : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding := Classical.choose hPair
  have hA : A.Irreducible := (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  have hRigid : ∀ a : Embedding A D, SameCopy a e → a = e :=
    fun a ha => ordered_embedding_eq_of_sameCopy a e ha
  have hInterior : ∀ μ : Fin ((q :: tail).length + 1),
      0 < μ.val → μ.val < (q :: tail).length →
      ∀ (i : W.Index) (p r : SharedOldACarrierEdge A stage.system.toRelStructure S),
        stage.train.rel μ p.1 r.1 ↔ W.train.rel μ
          (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
            S E.toRelStructure RF i p)
          (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
            S E.toRelStructure RF i r) := by
    intro μ _ _ i p r
    exact originalSharedTrain_iff_of_selectedFt_embeddings
      A stage.system.toRelStructure S E.toRelStructure RF
      stage.train W.train W.selectedTrain μ i p r
  have hCoreProjects := projectsACopies_relabel_of_fineEdges A D W.core e W.fineEdges
  obtain ⟨bounds, a, b, hTwo⟩ :=
    PhysicalForestStage.sameVectorAttachmentBounds_of_finiteMixed stage
      hA hBaseLinear e hRigid active E f W.train hReady.2 hSelectedStrong hTargetTwo
      hCutoff hInterior W.positiveFull hPair hCoreProjects W.supportNonempty
      W.supportCovers W.selectedSupports W.mixedForest W.fineParameters
  have hCarrierRigid : ∀ c d : Embedding A E.toRelStructure, SameCopy c d → c = d :=
    fun c d h => ordered_embedding_eq_of_sameCopy c d h
  obtain ⟨hStep, hBottom⟩ :=
    PhysicalForestStage.activeAttachment_pictureStep_and_bottom_of_physicalFt stage
      hA hBaseLinear e hRigid active E f W.train bounds hReady.1 hReady.2 a b
      hTwo W.selectedSupports W.mixedForest κ hCarrierRigid W.physicalArrow
  let next := PhysicalForestStage.activeAttachment_of_bounds
    stage hA hBaseLinear e hRigid active E f W.train bounds
  have hNextProject : next.system.toRelStructure.IsHomomorphism D next.system.part :=
    StructuralRamsey.Partite.Attachment.isHomomorphism_of_partProjections
      stage.system S E f D hProject
      (StructuralRamsey.Partite.System.isHomomorphism_relabel_of_partProjection
        W.core A D e hCoreProject)
  exact ⟨next.withBottom hBottom, hNextProject, hStep⟩

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

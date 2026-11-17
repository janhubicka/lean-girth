import Girth.TrainCoverageFreePhysicalAttachment
import Girth.TrainCoverageFreePhysicalFineForestAssertion
import Girth.TrainCoverageFreePhysicalPositiveTransfer
import Girth.TrainCoverageFreeExactLocalTrain
import Girth.TrainFillingRawCutoffTwoData
import Girth.TrainPhysicalEdgeToEmbeddingArrow
import Girth.TrainPhysicalRelationProjection

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P Y I : Type v}

/-- At cutoff two the filled local witness supplies linearity and strong
selected copies. The attachment itself gives the new mixed forest through
two and preserves the full system bounds on all original positive cuts. -/
theorem CutoffTwoRawLocalData.toProjectedForestStep
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nontrivial UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (2 :: tail).length}
    {allowed : Fin ((2 :: tail).length + 1) → Set P}
    (stage : PhysicalForestStage A₀.ordered B D family (2 :: tail) targetTrain allowed)
    (e : Embedding A₀.ordered D)
    (active : StructuralRamsey.Partite.ProjectedEmbedding A₀.ordered stage.system e.toFunctionEmbedding)
    (κ : Type w) [Nonempty κ] [Finite Y] [Finite I]
    (W : CutoffTwoRawLocalData (Y := Y) (I := I) A₀.ordered
      (actualActiveSubsystemPartite A₀.ordered stage.system e.toFunctionEmbedding)
      tail (stage.activeFineTrain e) (fun ν => e.toFunctionEmbedding ⁻¹' allowed ν) κ)
    (ht : Admissible (2 :: tail))
    (hProject : stage.system.toRelStructure.IsHomomorphism D stage.system.part)
    (hBaseLinear : ALinear A₀.ordered D)
    (hCovered : stage.CoversBase)
    (hBaseStrong : ∀ b ∈ family, AStrong A₀.ordered D (copyCarrier b))
    (hTargetTwo : ∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b) :
    ∃ next : PhysicalForestStage A₀.ordered B D family (2 :: tail) targetTrain allowed,
      next.system.toRelStructure.IsHomomorphism D next.system.part ∧
      PictureStep stage next e.toFunctionEmbedding κ := by
  classical
  let A := A₀.ordered
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  let E := W.system.relabel e.toFunctionEmbedding
  let f (i : I) := activePartiteToRelabelledCore A stage.system e.toFunctionEmbedding
    W.system (W.selected i)
  let U := W.train
  let hA : A.Irreducible := (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  have hRigid : ∀ a : Embedding A D, SameCopy a e → a = e :=
    fun a h => ordered_embedding_eq_of_sameCopy a e h
  have hStrong (b : DesignatedCopy B D stage.system family) (_ : b ∈ stage.selected) :
      AStrong A D (copyCarrier b.base) := hBaseStrong b.base b.base_mem
  have hCutoff (j : Fin (2 :: tail).length) :
      2 ≤ (2 :: tail).get j := ht.two_le _ (List.get_mem _ _)
  have hInterior (μ : Fin ((2 :: tail).length + 1)) (_ : 0 < μ.val)
      (_ : μ.val < (2 :: tail).length) (i : I)
      (a b : SharedOldACarrierEdge A stage.system.toRelStructure S) :
      stage.train.rel μ a.1 b.1 ↔
        U.rel μ
          (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure S E.toRelStructure
            (fun k => (f k).toEmbedding) i a)
          (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure S E.toRelStructure
            (fun k => (f k).toEmbedding) i b) :=
    originalSharedTrain_iff_of_selectedFt_embeddings
      A stage.system.toRelStructure S E.toRelStructure (fun k => (f k).toEmbedding)
      stage.train U W.selectedTrain μ i a b
  have hPositive (j : Fin (2 :: tail).length) (hj : 0 < j.val) :
      (activeGluingWitnessOrderOneData A stage.system e.toFunctionEmbedding
        E.toRelStructure (fun k => (f k).toEmbedding) U j.castSucc).FullSystemGirthGT
          ((2 :: tail).get j) := by
    let k : Fin tail.length := ⟨j.val - 1, by have := j.isLt; simp at this; omega⟩
    have hjk : k.succ = j := Fin.ext (by simp [k]; omega)
    rw [← hjk]
    change (W.train.carrierCutData (fun i => copyCarrier (W.selected i).toEmbedding)
      k.castSucc.succ).FullSystemGirthGT (tail.get k)
    exact W.positive k
  have hOut := PhysicalForestStage.actual_positive_full_of_Ft stage hA hBaseLinear
    e hRigid active E f U hCovered hStrong hTargetTwo hCutoff hInterior hPositive
  let bounds : ActiveAttachmentBounds stage hA e active E f U := by
    refine {
      coreProjectsACopies := projectsACopies_relabel_of_fineEdges A D W.system e W.fineEdges
      coreSupportNonempty := W.supportNonempty
      coreSupportCovers := W.supportCovers
      baseStrong := hStrong
      targetTwo := hTargetTwo
      interior := hInterior
      bottomTwo := by simp
      localForest := Or.inl (by simp)
      coreGirth := by simp
      cutoffTwo := fun _ => ⟨W.aLinear, W.strong⟩
      coreParameters := W.parameters
      interiorFull := ?_
      tailSupreme := fun j hj => (hOut j hj).2 }
    intro μ hPos hLt
    let j : Fin (2 :: tail).length := ⟨μ.val, hLt⟩
    have hIndex : j.castSucc = μ := Fin.ext rfl
    have h := hPositive j hPos
    rw [hIndex] at h
    exact ⟨h.1, fun n C hAccept hOrder =>
      h.2 n C hAccept (Nat.le_trans hOrder (Nat.mul_le_mul_left 2 (hCutoff j)))⟩
  refine ⟨PhysicalForestStage.activeAttachment_of_bounds stage hA hBaseLinear
    e hRigid active E f U bounds, ?_, ?_⟩
  · exact StructuralRamsey.Partite.Attachment.isHomomorphism_of_partProjections stage.system S E f D
      hProject (StructuralRamsey.Partite.System.isHomomorphism_relabel_of_partProjection
        W.system A D e W.projection)
  · apply PhysicalForestStage.activeAttachment_pictureStep_of_familyArrow
      stage hA hBaseLinear e hRigid active E f U bounds κ
    exact ordered_embeddingArrow_of_physicalEdgeArrow (A₀ := A₀)
      (fun i => (f i).toEmbedding) W.arrow

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

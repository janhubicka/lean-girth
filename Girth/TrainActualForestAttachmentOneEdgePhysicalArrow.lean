import Girth.TrainActualForestAttachmentOrderStepOneEdge
import Girth.TrainPhysicalEdgeToEmbeddingArrow

set_option autoImplicit false
set_option Elab.async false

/-!
# One-edge local target: physical F_t edge-colouring Ramsey arrow

The single-edge local active target still needs to produce the
actual selected PictureStep on embeddings. Its original F_t witness
colours physical A-edges, not arbitrary A-embeddings.

Under ambient A-copy image-rigidity (automatic for finite ordered
structures), the checked physical-edge-to-embedding bridge converts
this arrow without changing the colours, the selected gluing images
or any physical edge/wagon label. Combined with the honest
duplicate-one-edge forest lemma, the entire one-edge local branch
then uses the physical F_t arrow rather than an extra embedding-arrow
oracle.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (RelStructure.Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

section SingleEdgePhysicalArrow

variable (stage : ForestTailStage A B D family (q :: tail) targetTrain allowed)
variable (hA : A.Irreducible) [Finite UA] [Nontrivial UA]
variable (hBaseLinear : ALinear A D) (e : Embedding A D)
variable (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L P Y) [Finite Y] [Finite I]
variable (f : I → StructuralRamsey.Partite.Embedding
  (stage.system.induce (activeCarrier A stage.system e.toFunctionEmbedding)) E)
variable (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) (q :: tail).length)
variable (bounds : ActiveAttachmentBounds stage hA e active E f U)

local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "RF" => (fun i : I => (f i).toEmbedding)
local notation "OldBottom" => selectedPictureOrderOneData
  A B D stage.system family stage.selected stage.train
  (⟨0, by simp⟩ : Fin ((q :: tail).length + 1))

/-- The entire single-edge local OrderStage step from a PHYSICAL
edge-colouring arrow, with no two-A-source-edge assumption. A later
ordered corollary discharges hCarrierRigid from finite source order. -/
theorem ForestTailStage.activeAttachment_orderPictureStep_of_singleEdge_physicalArrow
    (hOldBottom : (OldBottom).FullSystemGirthGT q)
    (hBaseCovered : stage.CoversBase)
    (hCoreLinear : ALinear A E.toRelStructure)
    (hCoreStrong : ∀ i : I,
      AStrong A E.toRelStructure (copyCarrier (RF i)))
    (oneEdge : Set Y)
    (hAllCopies : ∀ i : I,
      bSupportPiece A (RF i) = HypergraphPiece.oneEdge oneEdge)
    (hAllEdges : ∀ edge : OldACarrierEdge A E.toRelStructure,
      edge.1 = oneEdge)
    (κ : Type w) [Nonempty κ]
    (hCarrierRigid :
      ∀ c d : Embedding A E.toRelStructure, SameCopy c d → c = d)
    (hPhysicalArrow :
      ∀ χ : OldACarrierEdge A E.toRelStructure → κ,
        ∃ i : I,
          ∀ c d : Embedding A (stage.system.induce S).toRelStructure,
            χ (actualEdge ((RF i).comp c)) =
              χ (actualEdge ((RF i).comp d))) :
    ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
      PictureStep stage R.toForestTailStage e.toFunctionEmbedding κ := by
  have hEmbeddingArrow :
      ∀ χ : Embedding A E.toRelStructure → κ,
        ∃ i : I,
          ∀ c d : Embedding A (stage.system.induce S).toRelStructure,
            χ ((RF i).comp c) = χ ((RF i).comp d) :=
    embeddingArrow_of_physicalEdgeArrow RF hCarrierRigid hPhysicalArrow
  exact stage.activeAttachment_orderPictureStep_of_singleEdge
    hA hBaseLinear e hRigid active E f U bounds
    hOldBottom hBaseCovered hCoreLinear hCoreStrong
    oneEdge hAllCopies hAllEdges κ hEmbeddingArrow

end SingleEdgePhysicalArrow
end StructuralRamsey.Girth.TrainRecursiveWitness

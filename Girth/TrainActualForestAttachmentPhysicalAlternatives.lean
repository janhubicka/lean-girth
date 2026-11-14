import Girth.TrainActualForestAttachmentPhysicalArrow
import Girth.TrainActualForestAttachmentOneEdgePhysicalArrow

set_option autoImplicit false
set_option Elab.async false

/-!
# One physical-arrow forest-to-order picture step: both local cases

For a nontrivial active A-support target, the local F_q Ramsey
witness provides an actual finite mixed forest through the SAME q,
one designated support copy per image and two distinct source edges.
If the active A-support has only one edge, choose the elementary
one-edge local witness; every named piece is the same one-edge
member and its indexed repetitions form a forest.

Both alternatives use the SAME physical A-edge-colouring Ramsey
arrow, converted to the checked A-embedding arrow only under
the explicit image-rigidity property (automatic for ordered A).

The output uses the real partite attachment, its selected B-copy
labels, all ambient physical edges, and its original train
parameters. No unspecified lower-rank witness is constructed here.
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

section LocalPhysicalAlternative

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

/-- Under EITHER genuine local forest alternative, a physical F_t
edge-colouring arrow produces one selected Ramsey picture step into
an actual ORDER stage with bottom q and all original positive cut
system bounds. This is the single per-fibre interface for the
later finite Ready induction. -/
theorem ForestTailStage.activeAttachment_orderPictureStep_of_physical_local_alternatives
    (hOldBottom : (OldBottom).FullSystemGirthGT q)
    (hBaseCovered : stage.CoversBase)
    (hAlternative :
      (∃ (a b : Embedding A (stage.system.toRelStructure.induce S)),
        ¬ SameCopy a b ∧
        Function.Injective (fun i : I => copyCarrier (RF i)) ∧
        FiniteMixedForestThrough (RelationalMixedSupportTest A RF) q)
      ∨
      (ALinear A E.toRelStructure ∧
        (∀ i : I, AStrong A E.toRelStructure (copyCarrier (RF i))) ∧
        (∃ edge : Set Y,
          (∀ i : I, bSupportPiece A (RF i) =
            HypergraphPiece.oneEdge edge) ∧
          (∀ actual : OldACarrierEdge A E.toRelStructure,
            actual.1 = edge))))
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
  rcases hAlternative with ⟨a, b, hTwoSource, hDistinct, hMixed⟩ |
      ⟨hCoreLinear, hCoreStrong, edge, hAllCopies, hAllEdges⟩
  · exact stage.activeAttachment_orderPictureStep_of_finiteMixed_physicalArrow
      hA hBaseLinear e hRigid active E f U bounds
      hOldBottom hBaseCovered a b hTwoSource hDistinct hMixed
      κ hCarrierRigid hPhysicalArrow
  · exact stage.activeAttachment_orderPictureStep_of_singleEdge_physicalArrow
      hA hBaseLinear e hRigid active E f U bounds
      hOldBottom hBaseCovered hCoreLinear hCoreStrong
      edge hAllCopies hAllEdges κ hCarrierRigid hPhysicalArrow

end LocalPhysicalAlternative
end StructuralRamsey.Girth.TrainRecursiveWitness

import Girth.TrainActualForestAttachmentOrderStep
import Girth.TrainActualBottomSingleEdgeLocalPreservation
import Girth.TrainSharedSupportInteriorCompatibility
import Girth.TrainActualSelectedOutputGirth
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# One-edge local active target: the finite order-stage picture step

The finite forest-to-order conversion applies a local Ramsey witness
to the active target of each picture step. Even when the outer selected
B-target has at least two support edges, an intermediate active target
may have only one. This local case requires neither two distinct
source A-edges nor injectivity of its repeated one-edge supports.

The genuine local bottom family is a forest of repeated copies of
one physical edge (star join tree). Under the explicit one-edge
geometry, the full bottom preservation theorem and existing actual
selected-copy label equivalence give the new order-stage bound.
The finite partite construction and its selected Ramsey map are
unchanged. This complements the nontrivial finite-mixed branch.
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

section SingleEdgeOrderAttachment

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
local notation "Shared" => activeCarrier_all_standard_copies_meet_core
  A stage.system e.toFunctionEmbedding active I
local notation "Selected" =>
  {r : DesignatedCopy B D stage.system family // r ∈ stage.selected}
local notation "Train" => generatedActualASupportTrain
  A hA stage.system.toRelStructure S E.toRelStructure RF
  stage.train U Shared
local notation "Bottom" => (⟨0, by simp⟩ : Fin ((q :: tail).length + 1))
local notation "OldBottom" => selectedPictureOrderOneData
  A B D stage.system family stage.selected stage.train Bottom
local notation "RawBottom" => attachedSelectedPictureOrderOneData
  A hA B D stage.system family stage.selected e E.toRelStructure
  RF stage.train U Shared Bottom
local notation "Attached" =>
  StructuralRamsey.Partite.Attachment.attach stage.system S E f
local notation "ActualBottom" => selectedPictureOrderOneData
  A B D Attached family
    (transportedSelectedCopies B D stage.system family stage.selected S E f)
    Train Bottom

/-- Actual finite picture step for the one-edge LOCAL active target,
with the original B-copy labels and the entire ordered train retained.
No F_t two-source-edge/injective-support premise is introduced. -/
theorem ForestTailStage.activeAttachment_orderPictureStep_of_singleEdge
    (hOldBottom : (OldBottom).FullSystemGirthGT q)
    (hBaseCovered : stage.CoversBase)
    (hCoreLinear : ALinear A E.toRelStructure)
    (hCoreStrong : ∀ i : I, AStrong A E.toRelStructure (copyCarrier (RF i)))
    (oneEdge : Set Y)
    (hAllCopies : ∀ i : I,
      bSupportPiece A (RF i) = HypergraphPiece.oneEdge oneEdge)
    (hAllEdges : ∀ edge : OldACarrierEdge A E.toRelStructure,
      edge.1 = oneEdge)
    (κ : Type w) [Nonempty κ]
    (hArrow : ∀ χ : Embedding A E.toRelStructure → κ,
      ∃ i : I, ∀ c d : Embedding A (stage.system.induce S).toRelStructure,
        χ ((f i).toEmbedding.comp c) = χ ((f i).toEmbedding.comp d)) :
    ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
      PictureStep stage R.toForestTailStage e.toFunctionEmbedding κ := by
  let newStage := stage.activeAttachment_of_local_bounds
    hA hBaseLinear e hRigid active E f U bounds
  have hPhysical : ALinear A
      (RelStructure.Attachment.attach
        stage.system.toRelStructure S E.toRelStructure RF) := by
    exact newStage.aLinear
  have hAllBaseStrong : ∀ b : Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b) :=
    ActiveAttachmentBounds.all_base_strong_of_covered
      stage hA e active E f U bounds hBaseCovered
  have hStrong : ∀ r : Selected,
      AStrong A D (copyCarrier r.1.base) :=
    fun r => bounds.baseStrong r.1 r.2
  obtain ⟨aB, bB, hDifferent⟩ := bounds.targetTwo
  have hTwo : ∀ r : Selected, ∃ e₁ e₂ : OldACarrierEdge A stage.system.toRelStructure,
      e₁ ≠ e₂ ∧ e₁.1 ⊆ copyCarrier r.1.embedding ∧
        e₂.1 ⊆ copyCarrier r.1.embedding :=
    fun r => selectedCopy_two_edges_of_target
      A B D stage.system family stage.selected r aB bB hDifferent
  have hActiveStrong : AStrong A stage.system.toRelStructure S :=
    activeCarrier_aStrong_of_base_aLinear
      A D stage.system hA stage.isPartite hBaseLinear e hRigid
  have hRel : ∀ (ν : Fin ((q :: tail).length + 1)) (j : I)
      (p r : SharedOldACarrierEdge A stage.system.toRelStructure S),
      stage.train.rel ν p.1 r.1 ↔
      U.rel ν
        (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
          S E.toRelStructure RF j p)
        (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
          S E.toRelStructure RF j r) := by
    apply sharedSupportTrainRel_of_interior stage.train U
      (sharedOldACarrierInclusion A stage.system.toRelStructure S)
      (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure S E.toRelStructure RF)
    intro ν hZero hTop j p r
    exact bounds.interior ν (by omega) (by omega) j p r
  have hRaw : (RawBottom).FullSystemGirthGT q :=
    attachedSelectedPicture_bottom_fullSystemGirth_of_singleEdgeLocal
      A hA B D stage.system family stage.selected e E.toRelStructure
      RF stage.train U Shared hRel
      hPhysical hCoreLinear hAllBaseStrong hTwo hActiveStrong hCoreStrong
      q hOldBottom oneEdge hAllCopies hAllEdges
  have hActual : (ActualBottom).FullSystemGirthGT q :=
    (attachedSelectedPicture_fullSystemGirth_iff_actualSelected
      A hA B D stage.system family stage.selected e E f
      stage.train U Shared Bottom hStrong hTwo q).mp hRaw
  exact stage.activeAttachment_orderPictureStep_of_actualBottom
    hA hBaseLinear e hRigid active E f U bounds hActual κ hArrow

end SingleEdgeOrderAttachment
end StructuralRamsey.Girth.TrainRecursiveWitness

import Girth.TrainSelectedPictureStageAssembly
import Girth.TrainActualBottomForestFromFiniteMixed
import Girth.TrainForestStageToOrderStage
import Girth.TrainActualSelectedOutputGirth
import Girth.ActiveCarrierStrong
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual finite picture step with bottom F_q -> an OrderStage

The existing ForestTailStage active attachment constructor preserves
the selected B-labels, all physical train relations, foresthood and
positive-coordinate system-girth. Its new bottom invariant is obtained
from the genuine local F_q mixed forest and the OLD bottom full
system-girth bound, using the complete source-level preservation proof.

The selected local Ramsey family is the SAME partite family used by
the attachment; support distinctness follows from one representative
per image. The actual full-system output is transported to the
selected-copy labels by the checked labelled equivalence, NOT by
forgetting copies with equal carriers.

The conclusion is a genuine next OrderStage and its existing selected
PictureStep. This is CONDITIONAL on the old bottom bound and on the
actual constructed local F_q witness. A global Ready induction over
the finite sequence of profiles remains separate.
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

section ActualOrderAttachment

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

/-- One real active local F_q witness gives the bottom system-girth
bound of the attached NEXT stage, from old bottom girth and the actual
selected family. No lower witness full girth or replacement of
the selected B-label index is assumed. -/
theorem ForestTailStage.activeAttachment_bottom_full_of_finiteMixed
    (hOldBottom : (OldBottom).FullSystemGirthGT q)
    (hAllBaseStrong : ∀ b : Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (a b : Embedding A (stage.system.toRelStructure.induce S))
    (hTwoSource : ¬ SameCopy a b)
    (hSelectedImages : Function.Injective
      (fun i : I => copyCarrier (RF i)))
    (hLocalMixed : FiniteMixedForestThrough
      (RelationalMixedSupportTest A RF) q) :
    (ActualBottom).FullSystemGirthGT q := by
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
    attachedSelectedPicture_bottom_fullSystemGirth_of_finiteMixed
      A hA B D stage.system family stage.selected e E.toRelStructure
      RF stage.train U Shared hRel q bounds.bottomTwo
      hOldBottom hAllBaseStrong hTwo hActiveStrong
      a b hTwoSource hSelectedImages hLocalMixed
  exact (attachedSelectedPicture_fullSystemGirth_iff_actualSelected
    A hA B D stage.system family stage.selected e E f
    stage.train U Shared Bottom hStrong hTwo q).mp hRaw

/-- The new attachment is an actual ORDER stage once the LOCAL same-q
forest produces its bottom bound. The finite Ramsey arrow at this
profile uses exactly the already constructed selected transition. -/
theorem ForestTailStage.activeAttachment_orderPictureStep_of_finiteMixed
    (hOldBottom : (OldBottom).FullSystemGirthGT q)
    (hAllBaseStrong : ∀ b : Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (a b : Embedding A (stage.system.toRelStructure.induce S))
    (hTwoSource : ¬ SameCopy a b)
    (hSelectedImages : Function.Injective
      (fun i : I => copyCarrier (RF i)))
    (hLocalMixed : FiniteMixedForestThrough
      (RelationalMixedSupportTest A RF) q)
    (κ : Type w) [Nonempty κ]
    (hArrow : ∀ χ : Embedding A E.toRelStructure → κ,
      ∃ i : I, ∀ c d : Embedding A (stage.system.induce S).toRelStructure,
        χ ((f i).toEmbedding.comp c) = χ ((f i).toEmbedding.comp d)) :
    ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
      PictureStep stage R.toForestTailStage e.toFunctionEmbedding κ := by
  let newStage := stage.activeAttachment_of_local_bounds
    hA hBaseLinear e hRigid active E f U bounds
  have hBottomRaw : (ActualBottom).FullSystemGirthGT q :=
    stage.activeAttachment_bottom_full_of_finiteMixed
      hA hBaseLinear e hRigid active E f U bounds
      hOldBottom hAllBaseStrong a b hTwoSource
      hSelectedImages hLocalMixed
  have hBottomNew :
      (selectedPictureOrderOneData
        A B D newStage.system family newStage.selected
        newStage.train Bottom).FullSystemGirthGT q := by
    exact hBottomRaw
  let R := newStage.withBottomSystemGirth hBottomNew
  refine ⟨R, ?_⟩
  exact stage.activeAttachment_pictureStep_of_familyArrow
    hA hBaseLinear e hRigid active E f U bounds κ hArrow

end ActualOrderAttachment
end StructuralRamsey.Girth.TrainRecursiveWitness

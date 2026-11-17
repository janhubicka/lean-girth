import Girth.TrainSelectedPictureMixedStageAssembly
import Girth.TrainActualMixedBoundsFromFiniteForest
import Girth.TrainActualBottomForestFromFiniteMixed
import Girth.TrainActualSelectedBaseCoverage
import Girth.TrainPhysicalEdgeToEmbeddingArrow
import Girth.TrainForestStageToOrderStage
import Girth.ActiveCarrierStrong

set_option autoImplicit false
set_option Elab.async false

/-!
# Real same-q F_t mixed forests give the NEXT selected OrderStage

This is the actual partite forest-to-order picture step with the
weaker and genuinely sufficient mixed-core attachment invariant.
It differs from the previous checked strong-core attachment only
in the treatment of irreducible core substructures:
  - a local core irreducible may be covered by an ambient A-copy;
  - OR by a selected complete local gluing copy, which is then
    transported using old selected B-or-A coverage.

The mixed-core ForestTailStage stage is already constructed by
TrainSelectedPictureMixedStageAssembly. The old bottom full-system
bound and local F_q finite SET forest through the SAME q imply
FULL bottom FullSystemGirthGT q on the actual selected output.
The new OrderStage adds only that bottom field; all positive
coordinates and actual train parameters are already present.

The same indexed PHYSICAL A-edge colouring arrow supplies an
actual selected PictureStep using finite ordered A-copy rigidity,
without assuming a stronger embedding arrow.

Unlike the earlier q=2 attempt, neither statement requests the
impossible IrreduciblesExtendTo A E property. The actual local
selected lower F_t stage supplies the three mixed-core fields.
Existence of the lower selected stage and its remaining bounds is
a separate finite F_t witness-production obligation.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

section MixedOrderStep

variable (stage : ForestTailStage A B D family (q :: tail) targetTrain allowed)
variable (hA : A.Irreducible) [Finite UA] [Nontrivial UA]
variable (hBaseLinear : ALinear A D) (e : Embedding A D)
variable (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L P Y) [Finite Y] [Finite I]
variable (f : I → StructuralRamsey.Partite.Embedding
  (stage.system.induce
    (activeCarrier A stage.system e.toFunctionEmbedding)) E)
variable (U : EdgeTrainLevels
  (OldACarrierEdge A E.toRelStructure) (q :: tail).length)
variable (bounds : ActiveAttachmentMixedBounds stage hA e active E f U)

local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "RF" => (fun i : I => (f i).toEmbedding)
local notation "Shared" => activeCarrier_all_standard_copies_meet_core
  A stage.system e.toFunctionEmbedding active I
local notation "Selected" => {r : DesignatedCopy B D stage.system family //
  r ∈ stage.selected}
local notation "Train" => generatedActualASupportTrain
  A hA stage.system.toRelStructure S E.toRelStructure RF
    stage.train U Shared
local notation "Bottom" => (⟨0, by simp⟩ :
  Fin ((q :: tail).length + 1))
local notation "OldBottom" =>
  selectedPictureOrderOneData A B D stage.system family
    stage.selected stage.train Bottom
local notation "RawBottom" =>
  attachedSelectedPictureOrderOneData A hA B D stage.system
    family stage.selected e E.toRelStructure RF stage.train U
    Shared Bottom
local notation "Attached" =>
  StructuralRamsey.Partite.Attachment.attach stage.system S E f
local notation "ActualBottom" =>
  selectedPictureOrderOneData A B D Attached family
    (transportedSelectedCopies B D stage.system family stage.selected
      S E f) Train Bottom

/-- Full ORIGINAL B-labelled bottom output system girth at q from
a genuine local SAME-q finite mixed forest, even when the core's
irreducibles do NOT all extend to an A-copy. Only the actual
selected base lifts, same-q forest and two active source A-copies
are used in addition to the weaker attachment bounds. -/
theorem ForestTailStage.activeAttachment_mixed_bottom_full_of_finiteMixed
    (hOldBottom : (OldBottom).FullSystemGirthGT q)
    (hBaseCovered : stage.CoversBase)
    (a b : Embedding A (stage.system.toRelStructure.induce S))
    (hTwoSource : ¬ SameCopy a b)
    (hSelectedSupports : Function.Injective
      (fun i : I => bSupportPiece A (RF i)))
    (hLocalMixed : FiniteMixedForestThrough
      (RelationalMixedSupportTest A RF) q) :
    (ActualBottom).FullSystemGirthGT q := by
  have hAllBaseStrong : ∀ b : Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b) :=
    stage.allBaseStrong_of_selected hBaseCovered bounds.baseStrong
  have hStrong : ∀ r : Selected,
      AStrong A D (copyCarrier r.1.base) :=
    fun r => bounds.baseStrong r.1 r.2
  obtain ⟨aB, bB, hDifferent⟩ := bounds.targetTwo
  have hTwo : ∀ r : Selected,
      ∃ e₁ e₂ : OldACarrierEdge A stage.system.toRelStructure,
        e₁ ≠ e₂ ∧ e₁.1 ⊆ copyCarrier r.1.embedding ∧
          e₂.1 ⊆ copyCarrier r.1.embedding :=
    fun r => selectedCopy_two_edges_of_target
      A B D stage.system family stage.selected
      r aB bB hDifferent
  have hActiveStrong : AStrong A stage.system.toRelStructure S :=
    activeCarrier_aStrong_of_base_aLinear
      A D stage.system hA stage.isPartite hBaseLinear e hRigid
  have hRel : ∀ (ν : Fin ((q :: tail).length + 1))
      (j : I) (p r : SharedOldACarrierEdge A
        stage.system.toRelStructure S),
      stage.train.rel ν p.1 r.1 ↔
      U.rel ν
        (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
          S E.toRelStructure RF j p)
        (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
          S E.toRelStructure RF j r) := by
    apply sharedSupportTrainRel_of_interior stage.train U
      (sharedOldACarrierInclusion A stage.system.toRelStructure S)
      (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
        S E.toRelStructure RF)
    intro ν hZero hTop j p r
    exact bounds.interior ν (by omega) (by omega) j p r
  have hSelectedImages : Function.Injective
      (fun i : I => copyCarrier (RF i)) :=
    activeGluingWitness_distinct_images_of_supportPiece_injective
      A stage.system e.toFunctionEmbedding E.toRelStructure RF
      hSelectedSupports
  have hRaw : (RawBottom).FullSystemGirthGT q :=
    attachedSelectedPicture_bottom_fullSystemGirth_of_finiteMixed
      A hA B D stage.system family stage.selected e E.toRelStructure
      RF stage.train U Shared hRel
      q bounds.bottomTwo hOldBottom hAllBaseStrong hTwo
      hActiveStrong a b hTwoSource hSelectedImages hLocalMixed
  exact (attachedSelectedPicture_fullSystemGirth_iff_actualSelected
    A hA B D stage.system family stage.selected e E f
      stage.train U Shared Bottom hStrong hTwo q).mp hRaw

/-- A genuine selected order-stage Ramsey PictureStep with the
literal F_q PHYSICAL A-edge colouring arrow, produced by the
MIXED-core attachment. There is NO local total A-irred-cover
assumption. The source A-copy rigidity is the genuine ordered
finite condition and is kept explicit in the generic theorem. -/
theorem ForestTailStage.activeAttachment_mixed_orderPictureStep_of_physicalFt
    (hOldBottom : (OldBottom).FullSystemGirthGT q)
    (hBaseCovered : stage.CoversBase)
    (a b : Embedding A (stage.system.toRelStructure.induce S))
    (hTwoSource : ¬ SameCopy a b)
    (hSelectedSupports : Function.Injective
      (fun i : I => bSupportPiece A (RF i)))
    (hLocalMixed : FiniteMixedForestThrough
      (RelationalMixedSupportTest A RF) q)
    (κ : Type w) [Nonempty κ]
    (hCarrierRigid : ∀ c d : Embedding A E.toRelStructure,
      SameCopy c d → c = d)
    (hPhysicalArrow :
      ∀ χ : OldACarrierEdge A E.toRelStructure → κ,
        ∃ i : I, ∀ c d : Embedding A (stage.system.induce S).toRelStructure,
          χ (actualEdge ((RF i).comp c)) =
            χ (actualEdge ((RF i).comp d))) :
    ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
      PictureStep stage R.toForestTailStage
        e.toFunctionEmbedding κ := by
  have hActualBottom : (ActualBottom).FullSystemGirthGT q :=
    stage.activeAttachment_mixed_bottom_full_of_finiteMixed
      hA hBaseLinear e hRigid active E f U bounds
      hOldBottom hBaseCovered a b hTwoSource
      hSelectedSupports hLocalMixed
  have hEmbeddingArrow :
      ∀ χ : Embedding A E.toRelStructure → κ,
        ∃ i : I,
          ∀ c d : Embedding A (stage.system.induce S).toRelStructure,
            χ ((RF i).comp c) = χ ((RF i).comp d) :=
    embeddingArrow_of_physicalEdgeArrow RF
      hCarrierRigid hPhysicalArrow
  let next : ForestTailStage A B D family
      (q :: tail) targetTrain allowed :=
    stage.activeAttachment_of_mixed_bounds
      hA hBaseLinear e hRigid active E f U bounds
  have hNextBottom :
      (selectedPictureOrderOneData A B D next.system family
        next.selected next.train Bottom).FullSystemGirthGT q :=
    hActualBottom
  let result : OrderStage A B D family
      (q :: tail) targetTrain allowed :=
    next.withBottomSystemGirth hNextBottom
  refine ⟨result, ?_⟩
  exact stage.activeAttachment_mixed_pictureStep_of_familyArrow
    hA hBaseLinear e hRigid active E f U bounds
    κ hEmbeddingArrow

end MixedOrderStep
end StructuralRamsey.Girth.TrainRecursiveWitness

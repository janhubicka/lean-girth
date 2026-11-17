import Girth.TrainCoverageFreePhysicalBoundsFromMixed
import Girth.TrainCoverageFreePhysicalOrderPass
import Girth.TrainActualBottomForestFromFiniteMixed
import Girth.TrainPhysicalEdgeToEmbeddingArrow
import Girth.ActiveCarrierStrong
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual coverage-free SAME-q F_t forest -> next selected PhysicalOrderStage

This is the genuine standalone F_t->R_t one-step source candidate.
Unlike the recursive ForestTailStage, the coverage-free PhysicalForestStage
does not demand any irreducible mixed coverage of the input or
local F_t witness. That missing property was the precise q=2
obstruction in the previous attempted stage implementation.

The output's genuine B-labelled bottom FullSystemGirthGT q comes
from the already developed original cycle/forest preservation
theorem applied to the same actual finite F_t mixed SET forest.
Selected complete-support injectivity is the exact one-image
condition of F_t. No ordinary support-edge or selected label is
deleted or replaced.

The next stage is constructed by the coverage-free actual
attachment and inherits all positive system-girth, partite
parameters, strong target copies and physical train restrictions.
Adding its bottom bound gives a coverage-free PhysicalOrderStage. The
physical A-edge colouring F_t arrow is converted to the actual
selected PictureStep only under finite ordered A-carrier rigidity.

The only local geometric requirements are explicitly those in
CoverageFree.ActiveAttachmentBounds, whose auxiliary forest/girth
and universal-top q2 fields follow from the SAME F_t mixed forest.

This remains an UNCOMPILED source candidate. The final local F_t
witness selection and exact fine-train compatibility have to be
identified with this attachment interface. This file alone does
not prove the unconditional universal F_t=>R_t assertion.
-/

/-!
Physical one-step SAME-q F_t mixed forest -> original B-labelled
bottom FullSystemGirthGT q and actual selected OrderStage PictureStep.
The active carrier uses only ProjectsACopies, not ordered
IsPartiteOver. Genuine original label/source transfer remains intact.
UNCOMPILED SOURCE.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

section MixedOrderStep

variable (stage : PhysicalForestStage A B D family (q :: tail) targetTrain allowed)
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
variable (bounds : ActiveAttachmentBounds stage hA e active E f U)

local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "RF" => (fun (i : I) => StructuralRamsey.Partite.Embedding.toEmbedding (f i))
local notation "Shared" => activeCarrier_all_standard_copies_meet_core
  A stage.system e.toFunctionEmbedding active I
local notation "Selected" => {r : DesignatedCopy B D stage.system family //
  r ∈ stage.selected}
local notation "Train" => generatedActualASupportTrain
  A hA stage.system.toRelStructure S E.toRelStructure RF
    stage.train U Shared
local notation "Bottom" => (Fin.mk 0 (Nat.zero_lt_succ (List.length (q :: tail))))
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

include hBaseLinear hRigid bounds in
/-- Full ORIGINAL B-labelled bottom output system girth at q from
a genuine local SAME-q finite mixed forest, even when the core's
irreducibles do NOT all extend to an A-copy. Only the actual
selected base lifts, same-q forest and two active source A-copies
are used in addition to the weaker attachment bounds. -/
theorem PhysicalForestStage.activeAttachment_bottom_full_of_finiteMixed
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
    PhysicalForestStage.allBaseStrong_of_selected stage hBaseCovered bounds.baseStrong
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
    activeCarrier_aStrong_of_projectedACopies
      A D stage.system stage.projectsACopies hBaseLinear e hRigid
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

local notation "Next" => PhysicalForestStage.activeAttachment_of_bounds
  stage hA hBaseLinear e hRigid active E f U bounds

include hA hBaseLinear hRigid active bounds in
/-- The actual attachment has bottom system girth and the selected picture
arrow. Keeping its system explicit lets callers carry other invariants. -/
theorem PhysicalForestStage.activeAttachment_pictureStep_and_bottom_of_physicalFt
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
    PictureStep stage Next e.toFunctionEmbedding κ ∧
      PhysicalForestStage.BottomReady Next := by
  have hActualBottom : (ActualBottom).FullSystemGirthGT q :=
    PhysicalForestStage.activeAttachment_bottom_full_of_finiteMixed stage
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
  exact ⟨PhysicalForestStage.activeAttachment_pictureStep_of_familyArrow stage
    hA hBaseLinear e hRigid active E f U bounds κ hEmbeddingArrow, hActualBottom⟩

include hA hBaseLinear hRigid active bounds in
/-- A genuine selected order-stage Ramsey PictureStep with the
literal F_q PHYSICAL A-edge colouring arrow, produced by the
MIXED-core attachment. There is NO local total A-irred-cover
assumption. The source A-copy rigidity is the genuine ordered
finite condition and is kept explicit in the generic theorem. -/
theorem PhysicalForestStage.activeAttachment_orderPictureStep_of_physicalFt
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
    ∃ R : PhysicalOrderStage A B D family (q :: tail) targetTrain allowed,
      PictureStep stage R.toPhysicalForestStage
        e.toFunctionEmbedding κ := by
  obtain ⟨hStep, hNextBottom⟩ :=
    PhysicalForestStage.activeAttachment_pictureStep_and_bottom_of_physicalFt stage
      hA hBaseLinear e hRigid active E f U bounds hOldBottom hBaseCovered
      a b hTwoSource hSelectedSupports hLocalMixed κ hCarrierRigid hPhysicalArrow
  exact ⟨(Next).withBottom hNextBottom, hStep⟩

end MixedOrderStep

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

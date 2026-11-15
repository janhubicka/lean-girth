import Girth.TrainCoverageFreeFinitePass
import Girth.TrainCoverageFreeBottomIncrement
import Girth.TrainSelectedPictureMixedStageAssembly
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual coverage-free F_t picture attachment: complete weak ForestStage

This is the standalone forest-to-order attachment step which the
circulation F_t axiom actually licenses. It is obtained by omitting
ONLY the recursive mixedCoverage requirement from the already
developed mixed-core selected attachment constructor.

The q=2 mixed K4-triangle obstruction shows that neither local
total A-irreducible coverage nor selected local-target-or-A mixed
coverage follows from an ARBITRARY F_t witness. Neither appears here.

The new ActiveAttachmentBounds stores the genuine F_t outputs:
  * local A-partiteness, A-support nonemptiness and vertex coverage;
  * literal selected base B-strongness and two source A-edges;
  * exact shared wagon-train compatibility;
  * the q-1 local forest / q-core-girth / universal top q=2 data;
  * local exact adjacent-part parameters and positive system bounds;
  * original B-labelled positive output SupremeCycleBound.

The checked source proof of the bottom selected forest increment
was already ported to CoverageFree.ForestStage. All other stage
fields are constructed by the SAME checked train/parameter/
selection/strongness lemmas used in TrainSelectedPictureStageAssembly.

The result is an actual coverage-free next stage, selected
TransitionEmbedding and Ramsey PictureStep, with ALL original
selected labels and physical A-edges retained. This stage has
no irrelevant mixedCoverage field to fill at q=2.

It remains a source-level Lean candidate requiring exact-head
compilation. Existence of the physical local F_t witness and its
exact positive certificates is separately necessary.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The standalone F_t attachment data. Unlike the previously
checked recursive stage, no irreducible mixed coverage is required. -/
structure ActiveAttachmentBounds
    (stage : ForestStage A B D family t targetTrain allowed)
    (hA : A.Irreducible) (e : Embedding A D)
    (active : StructuralRamsey.Partite.ProjectedEmbedding A stage.system e.toFunctionEmbedding)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (stage.system.induce (activeCarrier A stage.system e.toFunctionEmbedding)) E)
    (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) t.length) : Prop where
  corePartite : E.IsPartiteOver D
  coreSupportNonempty : Nonempty (OldACarrierEdge A E.toRelStructure)
  coreSupportCovers : ∀ y : Y,
    ∃ edge : OldACarrierEdge A E.toRelStructure, y ∈ edge.1
  baseStrong : ∀ b : DesignatedCopy B D stage.system family,
    b ∈ stage.selected → AStrong A D (copyCarrier b.base)
  targetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b
  interior : ∀ μ : Fin (t.length + 1), 0 < μ.val → μ.val < t.length →
    ∀ (i : I) (p q : SharedOldACarrierEdge A stage.system.toRelStructure
      (activeCarrier A stage.system e.toFunctionEmbedding)),
      stage.train.rel μ p.1 q.1 ↔ U.rel μ
        (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding) E.toRelStructure
          (fun i => (f i).toEmbedding) i p)
        (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding) E.toRelStructure
          (fun i => (f i).toEmbedding) i q)
  bottomTwo : 2 ≤ t.headD 0
  localForest : t.headD 0 = 2 ∨
    ((∃ e₀ e₁ : Set (activeCarrier A stage.system e.toFunctionEmbedding),
        e₀ ∈ supportCopies A (stage.system.induce
          (activeCarrier A stage.system e.toFunctionEmbedding)).toRelStructure ∧
        e₁ ∈ supportCopies A (stage.system.induce
          (activeCarrier A stage.system e.toFunctionEmbedding)).toRelStructure ∧
        e₀ ≠ e₁) ∧
      Function.Injective (fun i => bSupportPiece A (f i).toEmbedding) ∧
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A (fun i => (f i).toEmbedding)) (t.headD 0 - 1))
  coreGirth : 2 < t.headD 0 →
    GirthGT (supportCopies A E.toRelStructure) (t.headD 0)
  cutoffTwo : t.headD 0 = 2 →
    ∃ μ : Fin (t.length + 1), ∃ q : ℕ, 2 ≤ q ∧
      (activeGluingWitnessOrderOneData A stage.system e.toFunctionEmbedding
        E.toRelStructure (fun i => (f i).toEmbedding) U μ).FullSystemGirthGT q
  coreParameters : U.AdjacentParameters (fun edge => edge.1)
    (fun ν => E.part ⁻¹' allowed ν)
  interiorFull : ∀ μ : Fin (t.length + 1), 0 < μ.val → μ.val < t.length →
    (activeGluingWitnessOrderOneData A stage.system e.toFunctionEmbedding
      E.toRelStructure (fun i => (f i).toEmbedding) U μ).FullSystemGirthGT 2
  tailSupreme : ∀ j : Fin t.length, 0 < j.val →
    (attachedSelectedPictureOrderOneData A hA B D stage.system family stage.selected
      e E.toRelStructure (fun i => (f i).toEmbedding) stage.train U
      (activeCarrier_all_standard_copies_meet_core
        A stage.system e.toFunctionEmbedding active I) j.castSucc).SupremeCycleBound (t.get j)


section MixedAssembly

variable (stage : ForestStage A B D family t targetTrain allowed)
variable (hA : A.Irreducible) [Finite UA]
variable (hBaseLinear : ALinear A D) (e : Embedding A D)
variable (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding A stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L P Y) [Finite Y] [Finite I]
variable (f : I → StructuralRamsey.Partite.Embedding
  (stage.system.induce (activeCarrier A stage.system e.toFunctionEmbedding)) E)
variable (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) t.length)
variable (bounds : ActiveAttachmentBounds stage hA e active E f U)

local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "Attached" =>
  StructuralRamsey.Partite.Attachment.attach stage.system S E f
local notation "RF" => fun i => (f i).toEmbedding
local notation "Shared" => activeCarrier_all_standard_copies_meet_core
  A stage.system e.toFunctionEmbedding active I
local notation "Train" =>
  generatedActualASupportTrain A hA stage.system.toRelStructure S
    E.toRelStructure RF stage.train U Shared
local notation "Selected" =>
  transportedSelectedCopies B D stage.system family stage.selected S E f

/-- The actual next ForestStage with genuine mixed core coverage,
including the q=2 case where the original coreCoverage field could
be impossible. All outputs use the ORIGINAL selected B labels, full
physical edge family, exact train restriction and unchanged parts. -/
noncomputable def ForestStage.activeAttachment_of_bounds :
    ForestStage A B D family t targetTrain allowed := by
  classical
  have hActive : S.Nonempty := by
    have hSource : Nonempty UA := by
      by_contra hEmpty
      obtain ⟨a, b, hab⟩ := bounds.targetTwo
      apply hab
      have hEq : a = b := Embedding.ext (fun u => (hEmpty ⟨u⟩).elim)
      exact congrArg copyCarrier hEq
    obtain ⟨u⟩ := hSource
    exact ⟨active.val u, active, u, rfl⟩
  have hBottom := stage.activeAttachment_bottom_invariants_of_intrinsic
    hA hBaseLinear e hRigid hActive E f bounds.baseStrong
    bounds.bottomTwo bounds.localForest bounds.coreGirth U bounds.cutoffTwo
  let hStrong := fun q :
      {q : DesignatedCopy B D stage.system family // q ∈ stage.selected} =>
    bounds.baseStrong q.1 q.2
  have hTwo : ∀ q :
      {q : DesignatedCopy B D stage.system family // q ∈ stage.selected},
      ∃ r s : OldACarrierEdge A stage.system.toRelStructure,
        r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
          s.1 ⊆ copyCarrier q.1.embedding := by
    obtain ⟨a, b, hab⟩ := bounds.targetTwo
    exact fun q => selectedCopy_two_edges_of_target
      A B D stage.system family stage.selected q a b hab
  refine {
    Vertex := StructuralRamsey.Partite.Attachment.Vertex S (W := Y) (I := I)
    finiteVertex := inferInstance
    system := Attached
    isPartite := StructuralRamsey.Partite.Attachment.attach_isPartiteOver
      stage.system S E f stage.isPartite bounds.corePartite
    aLinear := aLinear_of_girthGT_two A Attached.toRelStructure
      (girthGT_mono hBottom.2.1 bounds.bottomTwo)
    supportNonempty := ?_
    supportCovers := activeAttachment_supportCovers
      A stage.system S E f stage.supportCovers bounds.coreSupportCovers
    selected := Selected
    selectedPhysicalInjective := transportedSelectedCopies_physical_injective
      A B D stage.system family stage.selected e E f
      hStrong hTwo stage.selectedPhysicalInjective
    strong := hBottom.2.2
    train := Train
    targetRestriction := ?_
    parameters := ?_
    bottomForest := hBottom.1
    tailGirth := ?_
  }
  · obtain ⟨edge⟩ := bounds.coreSupportNonempty
    obtain ⟨a, _⟩ := edge.2
    exact ⟨actualEdge
      ((StructuralRamsey.Partite.Attachment.coreEmbedding
        stage.system S E f).toEmbedding.comp a)⟩
  · rintro q ⟨i, old, hOld, rfl⟩ μ a₁ a₂
    exact (activeAttachment_standard_train_iff
      A hA stage.system S E f stage.train U Shared
      bounds.interior μ i (old.embedding.comp a₁) (old.embedding.comp a₂)).trans
        (stage.targetRestriction old hOld μ a₁ a₂)
  · apply activeAttached_actualASupport_allAdjacentParameters_of_intrinsic
      A hA stage.system e.toFunctionEmbedding active E f
      stage.train U allowed
      stage.parameters bounds.coreParameters bounds.interior
    intro μ hPos hLt
    exact Eq.mp (congrArg OrderOneData.Bound
      (activeGluingWitnessOrderOneData_eq_shared
        A stage.system e.toFunctionEmbedding E.toRelStructure RF U μ))
      (OrderOneData.bound_of_fullSystemGirth_ge_one _ 2
        (by omega) (bounds.interiorFull μ hPos hLt))
  · intro j hj
    have hGeometry :=
      attachedSelectedPicture_linear_and_strong_of_intrinsic
        A hA B D stage.system family stage.selected
        e active E.toRelStructure RF stage.train U
        bounds.interior stage.isPartite hBaseLinear hRigid
        j.castSucc (stage.tailGirth j hj).1 2
        (by omega) (bounds.interiorFull j.castSucc hj j.isLt)
    exact (attachedSelectedPicture_fullSystemGirth_iff_actualSelected
      A hA B D stage.system family stage.selected
      e E f stage.train U Shared j.castSucc
      hStrong hTwo (t.get j)).mp
        ⟨hGeometry.1, bounds.tailSupreme j hj⟩

/-- Each literal standard copy is a strong selected train
transition into the MIXED-core next stage. Only the original
selected family and exact physical parent restriction are used.
The change of local core-coverage field does not affect this map. -/
noncomputable def ForestStage.activeAttachment_transition
    (i : I) :
    TransitionEmbedding stage
      (stage.activeAttachment_of_bounds
        hA hBaseLinear e hRigid active E f U bounds) where
  toPartite := StructuralRamsey.Partite.Attachment.copyEmbedding
    stage.system S E f i
  map_selected := activeAttachment_standard_selected
    stage.system S E f B D family stage.selected i
  train_iff := fun μ a b => activeAttachment_standard_train_iff
    A hA stage.system S E f stage.train U Shared
    bounds.interior μ i a b

/-- The usual local homogeneous standard choice gives an actual
selected Ramsey PictureStep for the weaker mixed-core attachment.
The global output mixedCoverage is already certified by the
genuine lower-stage nested selected-gluing argument, and no
core IrreduciblesExtendTo A assumption appears. -/
theorem ForestStage.activeAttachment_pictureStep
    (κ : Type w)
    (hLocal : ∀ χ :
      StructuralRamsey.Partite.ProjectedEmbedding
        A E e.toFunctionEmbedding → κ,
      ∃ i : I,
        ∀ a b : StructuralRamsey.Partite.ProjectedEmbedding
          A stage.system e.toFunctionEmbedding,
        χ ((activeInduceProjected A a
          (projected_mem_activeCarrier A stage.system
            e.toFunctionEmbedding a)).comp (f i)) =
        χ ((activeInduceProjected A b
          (projected_mem_activeCarrier A stage.system
            e.toFunctionEmbedding b)).comp (f i))) :
    PictureStep stage
      (stage.activeAttachment_of_bounds
        hA hBaseLinear e hRigid active E f U bounds)
      e.toFunctionEmbedding κ := by
  intro χ
  obtain ⟨i, _, _, hi⟩ := activeAttachment_selected_train_selection
    A hA B D stage.system family stage.selected
    e.toFunctionEmbedding active E f stage.train U
    bounds.interior κ hLocal χ
  exact ⟨stage.activeAttachment_transition
    hA hBaseLinear e hRigid active E f U bounds i, hi⟩

/-- A PHYSICAL selected local F_t family can be fed through the
ordinary embedding-colouring interface: this selected mixed-core
picture step has exactly the same Ramsey-arrow premise as the
previous checked strong-core constructor, hence uses the same
ordered physical-edge conversion. -/
theorem ForestStage.activeAttachment_pictureStep_of_familyArrow
    (κ : Type w) [Nonempty κ]
    (hArrow : ∀ χ : Embedding A E.toRelStructure → κ,
      ∃ i : I,
        ∀ a b : Embedding A
          (stage.system.induce S).toRelStructure,
          χ ((f i).toEmbedding.comp a) =
            χ ((f i).toEmbedding.comp b)) :
    PictureStep stage
      (stage.activeAttachment_of_bounds
        hA hBaseLinear e hRigid active E f U bounds)
      e.toFunctionEmbedding κ :=
  stage.activeAttachment_pictureStep
    hA hBaseLinear e hRigid active E f U bounds κ
    (activeAttachment_localSelection_of_familyArrow
      A stage.system e.toFunctionEmbedding E f κ hArrow)

end MixedAssembly

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

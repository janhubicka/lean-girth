import Girth.TrainSelectedPictureStageAssembly
import Girth.TrainActualSelectedMixedCoreAttachment
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Free picture attachment stage under the CORRECT local mixed core cover

The previous ActiveAttachmentBounds demanded
IrreduciblesExtendTo A E for the complete local core.
At head q=2, this can be INCOMPATIBLE with A-strong selected local
targets containing an irreducible substructure supported by several
A-copies, even if ordinary A-support girth is >2.

The ACTUAL selected lower ForestTailStage has instead:
- a nonempty physical A-support edge set;
- every core vertex supported by an ambient A-edge;
- selected local gluing TARGET-copy OR ambient A-copy coverage of
  every irreducible core substructure.

The nested mixed-cover transfer in TrainSelectedMixedCoreAttachment
proves that the last property, together with old selected B-or-A
coverage, yields the EXACT output mixedCoverage required by the
ForestTailStage, retaining original selected B labels.

This module isolates the minimal change to the actual stage:
replace its single overstrong coreCoverage field by the three
genuinely available fields above. All other constructor steps
use the same checked bottom invariants, strongness, train,
parameters and positive-cut supreme transfer as the original
TrainSelectedPictureStageAssembly, without deleting edges or
assuming output girth.

The mixed field is an explicit certificate supplied by a real
selected lower F_t witness; this module does NOT yet produce that
witness or its finite Ramsey step.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The genuinely sufficient attachment specification. Only the
old overstrong IrreduciblesExtendTo A E field is replaced, by
actual core support and nested mixed-coverage data; every other
field is the same as in ActiveAttachmentBounds. -/
structure ActiveAttachmentMixedBounds
    (stage : ForestTailStage A B D family t targetTrain allowed)
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
  coreMixedCoverage :
    SelectedBorACoversIrreducibles A B D
      (StructuralRamsey.Partite.Attachment.attach stage.system
        (activeCarrier A stage.system e.toFunctionEmbedding) E f)
      family (transportedSelectedCopies B D stage.system family stage.selected
        (activeCarrier A stage.system e.toFunctionEmbedding) E f)
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

variable (stage : ForestTailStage A B D family t targetTrain allowed)
variable (hA : A.Irreducible) [Finite UA]
variable (hBaseLinear : ALinear A D) (e : Embedding A D)
variable (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding A stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L P Y) [Finite Y] [Finite I]
variable (f : I → StructuralRamsey.Partite.Embedding
  (stage.system.induce (activeCarrier A stage.system e.toFunctionEmbedding)) E)
variable (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) t.length)
variable (bounds : ActiveAttachmentMixedBounds stage hA e active E f U)

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

/-- The actual next ForestTailStage with genuine mixed core coverage,
including the q=2 case where the original coreCoverage field could
be impossible. All outputs use the ORIGINAL selected B labels, full
physical edge family, exact train restriction and unchanged parts. -/
noncomputable def ForestTailStage.activeAttachment_of_mixed_bounds :
    ForestTailStage A B D family t targetTrain allowed := by
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
    mixedCoverage := bounds.coreMixedCoverage
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

end MixedAssembly
end StructuralRamsey.Girth.TrainRecursiveWitness

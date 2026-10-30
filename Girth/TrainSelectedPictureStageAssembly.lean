import Girth.TrainSelectedPictureTransition
import Girth.TrainSelectedPictureStageForest
import Girth.TrainActualSelectedOutputGirth
import Girth.TrainActualIntrinsicParameters
import Girth.TrainSelectedPictureIntrinsicGeometry

set_option Elab.async false

/-!
# Assemble the actual next forest/tail stage

The previous interfaces proved the individual invariants of an attachment.
Here those results construct the literal next `ForestTailStage`, and the
actual standard embeddings then give its stronger selected `PictureStep`.
No completed output stage, output support coverage, selected injectivity,
train restriction, or output parameter condition is taken as an input.

The local data remain explicit: a finite partite core with irreducible-to-A
coverage, its forest/girth and adjacent parameters, interior compatibility
and intrinsic order-two full bounds, and the indexed output supreme-cycle
bounds. Output pretrain linearity is derived from intrinsic geometry. The last
condition is precisely the remaining positive-cut transfer obligation; it
is transported to actual selected labels by the genuine equivalence.
Neither existence of this local witness nor refinement readiness of the
remaining fibres follows merely by assembling these fields.
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

/-- Genuine local construction inputs. The tail field is the indexed
supreme-cycle condition, not output linearity or a completed next stage.
All other
fields concern the old stage, fixed target, or intrinsic core witness. -/
structure ActiveAttachmentBounds
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (hA : A.Irreducible) (e : Embedding A D)
    (active : StructuralRamsey.Partite.ProjectedEmbedding A stage.system e.toFunctionEmbedding)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (stage.system.induce (activeCarrier A stage.system e.toFunctionEmbedding)) E)
    (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) t.length) : Prop where
  corePartite : E.IsPartiteOver D
  coreCoverage : RelStructure.IrreduciblesExtendTo A E.toRelStructure
  baseStrong : ∀ b : DesignatedCopy B D stage.system family, b ∈ stage.selected →
    AStrong A D (copyCarrier b.base)
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

/-- Extending the empty irreducible supplies a genuine ambient A-edge,
without assuming an inhabited gluing-index family. -/
theorem supportNonempty_of_irreduciblesExtendTo
    (A : RelStructure L UA) (R : RelStructure L Y)
    (h : RelStructure.IrreduciblesExtendTo A R) :
    Nonempty (OldACarrierEdge A R) := by
  have hIrr : (R.induce (∅ : Set Y)).Irreducible := by
    intro a
    exact False.elim a.2
  obtain ⟨a, _⟩ := h ∅ hIrr
  exact ⟨actualEdge a⟩

/-- Core irreducible coverage already covers every vertex by a genuine
ambient A-edge. No coverage by the prescribed gluing images is required. -/
theorem supportCovers_of_irreduciblesExtendTo
    (A : RelStructure L UA) (R : RelStructure L Y)
    (h : RelStructure.IrreduciblesExtendTo A R) :
    ∀ y : Y, ∃ edge : OldACarrierEdge A R, y ∈ edge.1 := by
  intro y
  have hIrr : (R.induce ({y} : Set Y)).Irreducible := by
    intro a b hab
    exact (hab (Subsingleton.elim a b)).elim
  obtain ⟨a, ha⟩ := h {y} hIrr
  obtain ⟨u, hu⟩ := ha ⟨y, Set.mem_singleton y⟩
  exact ⟨actualEdge a, u, hu.symm⟩

/-- Vertex support coverage is preserved by the literal free attachment.
Its core vertices use core edges; private vertices use their own standard. -/
theorem activeAttachment_supportCovers
    {X : Type v} (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X) (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (hOld : ∀ x : X, ∃ edge : OldACarrierEdge A C.toRelStructure, x ∈ edge.1)
    (hCore : ∀ y : Y, ∃ edge : OldACarrierEdge A E.toRelStructure, y ∈ edge.1) :
    ∀ z : StructuralRamsey.Partite.Attachment.Vertex S (W := Y) (I := I),
      ∃ edge : OldACarrierEdge A
        (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure,
        z ∈ edge.1 := by
  rintro (y | ⟨i, x⟩)
  · obtain ⟨edge, hy⟩ := hCore y
    obtain ⟨a, ha⟩ := edge.2
    rw [ha] at hy
    obtain ⟨u, rfl⟩ := hy
    exact ⟨actualEdge ((StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding.comp a),
      u, rfl⟩
  · obtain ⟨edge, hx⟩ := hOld x.1
    obtain ⟨a, ha⟩ := edge.2
    rw [ha] at hx
    obtain ⟨u, hu⟩ := hx
    refine ⟨actualEdge
      ((StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding.comp a), u, ?_⟩
    change RelStructure.Attachment.copyMap C.toRelStructure S E.toRelStructure
      (fun i => (f i).toEmbedding) i (a u) = Sum.inr (i, x)
    rw [hu]
    exact RelStructure.Attachment.copyMap_not_mem i x.1 x.2

section Assembly

variable (stage : ForestTailStage A B D family t targetTrain allowed)
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
local notation "Attached" => StructuralRamsey.Partite.Attachment.attach stage.system S E f
local notation "RF" => fun i => StructuralRamsey.Partite.Embedding.toEmbedding (f i)
local notation "Shared" => activeCarrier_all_standard_copies_meet_core
  A stage.system e.toFunctionEmbedding active I
local notation "Train" => generatedActualASupportTrain A hA stage.system.toRelStructure S
  E.toRelStructure RF stage.train U Shared
local notation "Selected" => transportedSelectedCopies B D stage.system family stage.selected S E f

/-- Assemble every field of the next actual finite stage from the old
stage and the named local inputs. The only output cycle premise is the
explicit indexed supreme-cycle bound. Output pretrain linearity is
derived separately from the old stage and intrinsic core geometry. -/
noncomputable def ForestTailStage.activeAttachment_of_local_bounds :
    ForestTailStage A B D family t targetTrain allowed := by
  classical
  have hActive : (S).Nonempty := by
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
  let hStrong := fun q : {q : DesignatedCopy B D stage.system family // q ∈ stage.selected} =>
    bounds.baseStrong q.1 q.2
  have hTwo : ∀ q : {q : DesignatedCopy B D stage.system family // q ∈ stage.selected},
      ∃ r s : OldACarrierEdge A stage.system.toRelStructure, r ≠ s ∧
        r.1 ⊆ copyCarrier q.1.embedding ∧ s.1 ⊆ copyCarrier q.1.embedding := by
    obtain ⟨a, b, hab⟩ := bounds.targetTwo
    exact fun q => selectedCopy_two_edges_of_target
      A B D stage.system family stage.selected q a b hab
  refine {
    Vertex := StructuralRamsey.Partite.Attachment.Vertex S (W := Y) (I := I)
    finiteVertex := inferInstance
    system := Attached
    isPartite := StructuralRamsey.Partite.Attachment.attach_isPartiteOver
      stage.system S E f stage.isPartite bounds.corePartite
    aLinear := aLinear_of_girthGT_two A (Attached).toRelStructure
      (girthGT_mono hBottom.2.1 bounds.bottomTwo)
    supportNonempty := ?_
    supportCovers := activeAttachment_supportCovers A stage.system S E f stage.supportCovers
      (supportCovers_of_irreduciblesExtendTo A E.toRelStructure bounds.coreCoverage)
    selected := Selected
    selectedPhysicalInjective := transportedSelectedCopies_physical_injective
      A B D stage.system family stage.selected e E f hStrong hTwo stage.selectedPhysicalInjective
    mixedCoverage := selectedBorACoversIrreducibles_partiteAttachment
      A B D stage.system family stage.selected S E f stage.mixedCoverage bounds.coreCoverage
    strong := hBottom.2.2
    train := Train
    targetRestriction := ?_
    parameters := ?_
    bottomForest := hBottom.1
    tailGirth := ?_
  }
  · obtain ⟨edge⟩ := supportNonempty_of_irreduciblesExtendTo
      A E.toRelStructure bounds.coreCoverage
    obtain ⟨a, _⟩ := edge.2
    exact ⟨actualEdge
      ((StructuralRamsey.Partite.Attachment.coreEmbedding stage.system S E f).toEmbedding.comp a)⟩
  · rintro q ⟨i, old, hOld, rfl⟩ μ a₁ a₂
    exact (activeAttachment_standard_train_iff A hA stage.system S E f stage.train U
      Shared bounds.interior μ i (old.embedding.comp a₁) (old.embedding.comp a₂)).trans
        (stage.targetRestriction old hOld μ a₁ a₂)
  · apply activeAttached_actualASupport_allAdjacentParameters_of_intrinsic
      A hA stage.system e.toFunctionEmbedding active E f stage.train U allowed
      stage.parameters bounds.coreParameters bounds.interior
    intro μ hPos hLt
    exact Eq.mp (congrArg OrderOneData.Bound
      (activeGluingWitnessOrderOneData_eq_shared
        A stage.system e.toFunctionEmbedding E.toRelStructure RF U μ))
      (OrderOneData.bound_of_fullSystemGirth_ge_one _ 2 (by omega)
        (bounds.interiorFull μ hPos hLt))
  · intro j hj
    have hGeometry := attachedSelectedPicture_linear_and_strong_of_intrinsic
      A hA B D stage.system family stage.selected e active E.toRelStructure RF
      stage.train U bounds.interior stage.isPartite hBaseLinear hRigid
      j.castSucc (stage.tailGirth j hj).1 2 (by omega)
      (bounds.interiorFull j.castSucc hj j.isLt)
    exact (attachedSelectedPicture_fullSystemGirth_iff_actualSelected
      A hA B D stage.system family stage.selected e E f stage.train U Shared j.castSucc
      hStrong hTwo (t.get j)).mp ⟨hGeometry.1, bounds.tailSupreme j hj⟩

/-- Every actual standard is a selected train transition into the assembled
stage. This map is constructed, including reflection, rather than supplied. -/
noncomputable def ForestTailStage.activeAttachment_transition (i : I) :
    TransitionEmbedding stage
      (stage.activeAttachment_of_local_bounds hA hBaseLinear e hRigid active E f U bounds) where
  toPartite := StructuralRamsey.Partite.Attachment.copyEmbedding stage.system S E f i
  map_selected := activeAttachment_standard_selected
    stage.system S E f B D family stage.selected i
  train_iff := fun μ a b => activeAttachment_standard_train_iff
    A hA stage.system S E f stage.train U Shared bounds.interior μ i a b

/-- The ordinary local homogeneous standard choice is enough for the
stronger `PictureStep` once the actual stage fields are assembled. -/
theorem ForestTailStage.activeAttachment_pictureStep
    (κ : Type w)
    (hLocal : ∀ χ : StructuralRamsey.Partite.ProjectedEmbedding A E e.toFunctionEmbedding → κ,
      ∃ i : I, ∀ a b : StructuralRamsey.Partite.ProjectedEmbedding A stage.system e.toFunctionEmbedding,
        χ ((activeInduceProjected A a
          (projected_mem_activeCarrier A stage.system e.toFunctionEmbedding a)).comp (f i)) =
          χ ((activeInduceProjected A b
            (projected_mem_activeCarrier A stage.system e.toFunctionEmbedding b)).comp (f i))) :
    PictureStep stage
      (stage.activeAttachment_of_local_bounds hA hBaseLinear e hRigid active E f U bounds)
      e.toFunctionEmbedding κ := by
  intro χ
  obtain ⟨i, _, _, hi⟩ := activeAttachment_selected_train_selection
    A hA B D stage.system family stage.selected e.toFunctionEmbedding active E f
      stage.train U bounds.interior κ hLocal χ
  exact ⟨stage.activeAttachment_transition hA hBaseLinear e hRigid active E f U bounds i, hi⟩

/-- A usual Ramsey-family arrow on all relational A-embeddings in the
core yields the selected train picture step. Projected colouring
extension and the output transition are both constructed internally. -/
theorem ForestTailStage.activeAttachment_pictureStep_of_familyArrow
    (κ : Type w) [Nonempty κ]
    (hArrow : ∀ χ : Embedding A E.toRelStructure → κ,
      ∃ i : I, ∀ a b : Embedding A (stage.system.induce S).toRelStructure,
        χ ((f i).toEmbedding.comp a) = χ ((f i).toEmbedding.comp b)) :
    PictureStep stage
      (stage.activeAttachment_of_local_bounds hA hBaseLinear e hRigid active E f U bounds)
      e.toFunctionEmbedding κ :=
  stage.activeAttachment_pictureStep hA hBaseLinear e hRigid active E f U bounds κ
    (activeAttachment_localSelection_of_familyArrow
      A stage.system e.toFunctionEmbedding E f κ hArrow)

end Assembly
end StructuralRamsey.Girth.TrainRecursiveWitness

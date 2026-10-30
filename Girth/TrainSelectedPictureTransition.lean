import Girth.TrainRecursiveWitnessPass
import Girth.ForestSelectedMixedCoverage
import Girth.TrainGeneratedActualAllLevelRestriction
import Girth.TrainActualPhysicalEdgeCarrierEval
import Girth.TrainSharedSupportInteriorCompatibility
import Girth.TrainActualActiveSharedEdge

set_option Elab.async false

/-!
# The genuine standard embeddings supply selected train transitions

The local Ramsey family chooses a standard copy in the actual attachment.
That same standard embedding transports every selected copy with its exact
base label and preserves and reflects every generated train relation on
physical A-edges.  Compatibility is required only at interior cuts: the
bottom equality and universal top are automatic for the injective shared
edge maps.

The local homogeneous selection is strengthened here before a next
`ForestTailStage` is assembled.  Its output supplies exactly the selected
label and train clauses of `TransitionEmbedding`, in addition to the usual
picture property.  No output transition map or train-reflection premise is
assumed.  The local Ramsey family, the remaining stage invariants and the
preservation of unprocessed-fibre refinement readiness remain separate.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}

section StandardTransport

variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (C : StructuralRamsey.Partite.System L P X)
variable (S : Set X) (E : StructuralRamsey.Partite.System L P Y)
variable (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)

local notation "Std" => StructuralRamsey.Partite.Attachment.copyEmbedding C S E f
local notation "RF" => fun i => StructuralRamsey.Partite.Embedding.toEmbedding (f i)

/-- The physical edge of a genuinely composed A-embedding is exactly the
canonical standard edge in the attachment's edge presentation. -/
theorem actualEdge_standard_comp (i : I) (a : Embedding A C.toRelStructure) :
    actualEdge ((Std i).toEmbedding.comp a) =
      actualAPictureEdgeEquiv A hA C.toRelStructure S E.toRelStructure RF
        (physicalStandardEdge
          (sharedOldACarrierInclusion A C.toRelStructure S)
          (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure RF)
          i (actualEdge a)) := by
  apply Subtype.ext
  exact (copyCarrier_comp_eq_image (Std i).toEmbedding a).trans
    (actualAPictureEdgeEquiv_standard_carrier
      A hA C.toRelStructure S E.toRelStructure RF i (actualEdge a)).symm

/-- Each standard transports the prescribed selected family literally,
retaining the designated base label, even when different carriers agree. -/
theorem activeAttachment_standard_selected
    (B : RelStructure L VB) (D : RelStructure L P)
    (family : Set (Embedding B D))
    (selected : Set (DesignatedCopy B D C family))
    (i : I) (q : DesignatedCopy B D C family) (hq : q ∈ selected) :
    mapDesignated (Std i) q ∈
      transportedSelectedCopies B D C family selected S E f := by
  exact ⟨i, q, hq, rfl⟩

variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure S))

/-- A genuine standard embedding preserves and reflects every generated
train relation on actual A-copy edges.  Only interior shared compatibility
is requested; no output train law is assumed. -/
theorem activeAttachment_standard_train_iff
    (hInterior : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      ∀ (i : I) (p q : SharedOldACarrierEdge A C.toRelStructure S),
        T.rel μ p.1 q.1 ↔ U.rel μ
          (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure RF i p)
          (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure RF i q))
    (μ : Fin (m + 1)) (i : I)
    (a b : Embedding A C.toRelStructure) :
    (generatedActualASupportTrain A hA C.toRelStructure S E.toRelStructure RF
      T U hShared).rel μ
      (actualEdge ((Std i).toEmbedding.comp a))
      (actualEdge ((Std i).toEmbedding.comp b)) ↔
        T.rel μ (actualEdge a) (actualEdge b) := by
  have hRel := sharedSupportTrainRel_of_interior T U
    (sharedOldACarrierInclusion A C.toRelStructure S)
    (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure RF)
    (fun μ hZero hTop i p q => hInterior μ (by omega) (by omega) i p q)
  have hEdges := congrArg₂
    (fun r s => (generatedActualASupportTrain A hA C.toRelStructure S
      E.toRelStructure RF T U hShared).rel μ r s)
    (actualEdge_standard_comp A hA C S E f i a)
    (actualEdge_standard_comp A hA C S E f i b)
  exact (Iff.of_eq hEdges).trans (generatedActualASupportTrain_restrict_standard
    A hA C.toRelStructure S E.toRelStructure RF T U hRel hShared μ i
    (actualEdge a) (actualEdge b))

end StandardTransport

/-- A local core Ramsey family supplies a homogeneous *standard* map with
both clauses needed by a selected train transition.  The conclusion uses
all physical A-edges and every selected old label.  It does not assume a
completed next stage, a stronger picture property, or output train
reflection.
-/
theorem activeAttachment_selected_train_selection
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L VB) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (Embedding B D))
    (selected : Set (DesignatedCopy B D C family))
    (α : UA ↪ P)
    (active : StructuralRamsey.Partite.ProjectedEmbedding A C α)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C α)) E)
    {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
    (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) m)
    (hInterior : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      ∀ (i : I) (p q : SharedOldACarrierEdge A C.toRelStructure (activeCarrier A C α)),
        T.rel μ p.1 q.1 ↔ U.rel μ
          (sharedOldACarrierCoreEmbedding A C.toRelStructure (activeCarrier A C α)
            E.toRelStructure (fun i => (f i).toEmbedding) i p)
          (sharedOldACarrierCoreEmbedding A C.toRelStructure (activeCarrier A C α)
            E.toRelStructure (fun i => (f i).toEmbedding) i q))
    (κ : Type w)
    (hLocal : ∀ χ : StructuralRamsey.Partite.ProjectedEmbedding A E α → κ,
      ∃ i : I, ∀ a b : StructuralRamsey.Partite.ProjectedEmbedding A C α,
        χ ((activeInduceProjected A a (projected_mem_activeCarrier A C α a)).comp (f i)) =
          χ ((activeInduceProjected A b (projected_mem_activeCarrier A C α b)).comp (f i))) :
    let S := activeCarrier A C α
    let attached := StructuralRamsey.Partite.Attachment.attach C S E f
    let selected' := transportedSelectedCopies B D C family selected S E f
    let train := generatedActualASupportTrain A hA C.toRelStructure S E.toRelStructure
      (fun i => (f i).toEmbedding) T U
      (activeCarrier_all_standard_copies_meet_core A C α active I)
    ∀ χ : StructuralRamsey.Partite.ProjectedEmbedding A attached α → κ,
      ∃ i : I,
        let standard := StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i
        (∀ q : DesignatedCopy B D C family, q ∈ selected →
          mapDesignated standard q ∈ selected') ∧
        (∀ μ : Fin (m + 1), ∀ a b : Embedding A C.toRelStructure,
          train.rel μ (actualEdge (standard.toEmbedding.comp a))
            (actualEdge (standard.toEmbedding.comp b)) ↔
              T.rel μ (actualEdge a) (actualEdge b)) ∧
        (∀ a b : StructuralRamsey.Partite.ProjectedEmbedding A C α,
          χ (a.comp standard) = χ (b.comp standard)) := by
  dsimp only
  intro χ
  let S := activeCarrier A C α
  let core := StructuralRamsey.Partite.Attachment.coreEmbedding C S E f
  obtain ⟨i, hi⟩ := hLocal (fun a => χ (a.comp core))
  refine ⟨i, ?_, ?_, ?_⟩
  · intro q hq
    exact activeAttachment_standard_selected C S E f B D family selected i q hq
  · intro μ a b
    exact activeAttachment_standard_train_iff A hA C S E f T U
      (activeCarrier_all_standard_copies_meet_core A C α active I)
      hInterior μ i a b
  · intro a b
    rw [activeAttachment_copy_comp A C S E f i a (projected_mem_activeCarrier A C α a),
      activeAttachment_copy_comp A C S E f i b (projected_mem_activeCarrier A C α b)]
    exact hi a b

/-- The ordinary Ramsey arrow of the prescribed core family implies the
projected local selection needed by the attachment. Extend a projected
colouring arbitrarily on the other ambient A-embeddings; all active
embeddings used by the selected gluing map retain their prescribed colour.
No assumption that every core embedding has the active projection is used.
-/
theorem activeAttachment_localSelection_of_familyArrow
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C α)) E)
    (κ : Type w) [Nonempty κ]
    (hArrow : ∀ χ : Embedding A E.toRelStructure → κ,
      ∃ i : I, ∀ a b : Embedding A
        (C.induce (activeCarrier A C α)).toRelStructure,
        χ ((f i).toEmbedding.comp a) = χ ((f i).toEmbedding.comp b)) :
    ∀ χ : StructuralRamsey.Partite.ProjectedEmbedding A E α → κ,
      ∃ i : I, ∀ a b : StructuralRamsey.Partite.ProjectedEmbedding A C α,
        χ ((activeInduceProjected A a (projected_mem_activeCarrier A C α a)).comp (f i)) =
          χ ((activeInduceProjected A b (projected_mem_activeCarrier A C α b)).comp (f i)) := by
  classical
  intro χ
  let extended : Embedding A E.toRelStructure → κ := fun a =>
    if h : ∀ u : UA, E.part (a u) = α u then χ ⟨a, h⟩
    else Classical.choice (inferInstance : Nonempty κ)
  have hExtended (a : StructuralRamsey.Partite.ProjectedEmbedding A E α) :
      extended a.val = χ a := by
    simp only [extended, dite_eq_left a.property]
    exact congrArg χ (Subtype.ext rfl)
  obtain ⟨i, hi⟩ := hArrow extended
  refine ⟨i, ?_⟩
  intro a b
  let a' := activeInduceProjected A a (projected_mem_activeCarrier A C α a)
  let b' := activeInduceProjected A b (projected_mem_activeCarrier A C α b)
  exact (hExtended (a'.comp (f i))).symm.trans
    ((hi a'.val b'.val).trans (hExtended (b'.comp (f i))))

end StructuralRamsey.Girth.TrainRecursiveWitness

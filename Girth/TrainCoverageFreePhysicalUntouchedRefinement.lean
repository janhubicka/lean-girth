import Girth.TrainUntouchedRefinement
import Girth.TrainCoverageFreeACopyProjection

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {UA P X Y I : Type v}
variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered
local notation "hA" => RelStructure.HereditarilyIrreducible.irreducible
  (RelStructure.ordered_hereditarilyIrreducible A₀)

section EdgeEquiv

variable (D : RelStructure L.withOrder P)
variable (C : StructuralRamsey.Partite.System L.withOrder P X)

/-- Every actual edge of an active fibre projects to its base copy. -/
private theorem activePhysicalEdge_has_projectedCarrier_of_projectsACopies
    (hProjected : ProjectsACopies A D C) (β : Embedding A D)
    (a : SharedOldACarrierEdge A C.toRelStructure (activeCarrier A C β.toFunctionEmbedding)) :
    ∃ b : StructuralRamsey.Partite.ProjectedEmbedding A C β.toFunctionEmbedding,
      a.1.1 = copyCarrier b.val := by
  obtain ⟨b, hb⟩ := a.1.2
  obtain ⟨base, hBase⟩ := hProjected b
  have hSame : SameCopy base β := sameCopy_of_range_subset base β (by
    intro u
    have hActive : b u ∈ activeCarrier A C β.toFunctionEmbedding := by
      apply a.2
      rw [hb]
      exact ⟨u, rfl⟩
    have hp := activeCarrier_subset_support A C β.toFunctionEmbedding hActive
    change C.part (b u) ∈ Set.range β.toFunctionEmbedding at hp
    rw [← hBase u] at hp
    obtain ⟨w, hw⟩ := hp
    exact ⟨w, hw.symm⟩)
  have hEq := ordered_embedding_eq_of_sameCopy base β hSame
  refine ⟨⟨b, fun u => (hBase u).symm.trans (congrArg (fun k : Embedding A D => k u) hEq)⟩, hb⟩

variable (α β : Embedding A₀.ordered D)
variable (E : StructuralRamsey.Partite.System L.withOrder P Y)
variable (f : I → StructuralRamsey.Partite.Embedding
  (C.induce (activeCarrier A₀.ordered C α.toFunctionEmbedding)) E)

local notation "S" => activeCarrier A C α.toFunctionEmbedding
local notation "Out" => StructuralRamsey.Partite.Attachment.attach C S E f
local notation "Std" => StructuralRamsey.Partite.Attachment.copyEmbedding C S E f
local notation "OldActive" =>
  SharedOldACarrierEdge A C.toRelStructure (activeCarrier A C β.toFunctionEmbedding)
local notation "NewActive" =>
  SharedOldACarrierEdge A₀.ordered
    (StructuralRamsey.Partite.System.toRelStructure
      (StructuralRamsey.Partite.Attachment.attach C S E f))
    (activeCarrier A₀.ordered (StructuralRamsey.Partite.Attachment.attach C S E f)
      β.toFunctionEmbedding)

private theorem untouchedActiveEdge_private_vertex_of_projectsACopies
    (hOld : ProjectsACopies A D C) (hDifferent : α ≠ β) (a : OldActive) :
    ∃ x : X, x ∈ a.1.1 ∧ x ∉ S := by
  classical
  by_contra hNo
  obtain ⟨edge, hEdge⟩ := activePhysicalEdge_has_projectedCarrier_of_projectsACopies A₀ D C hOld β a
  have hSame : SameCopy β α := sameCopy_of_range_subset β α (by
    intro u
    have hMem : edge.val u ∈ a.1.1 := by
      rw [hEdge]
      exact ⟨u, rfl⟩
    have hActive : edge.val u ∈ S := by
      by_contra h
      exact hNo ⟨edge.val u, hMem, h⟩
    have hPart := activeCarrier_subset_support A C α.toFunctionEmbedding hActive
    change C.part (edge.val u) ∈ Set.range α.toFunctionEmbedding at hPart
    rw [edge.property u] at hPart
    obtain ⟨w, hw⟩ := hPart
    exact ⟨w, hw.symm⟩)
  exact hDifferent (ordered_embedding_eq_of_sameCopy α β hSame.symm)

private theorem standardActiveEdge_pair_injective_of_projectsACopies
    (hOld : ProjectsACopies A D C) (hDifferent : α ≠ β) :
    Function.Injective (fun ia : I × OldActive =>
      standardActiveEdge A C S E f β.toFunctionEmbedding ia.1 ia.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hEq
  have hImage := congrArg (fun q : NewActive => q.1.1) hEq
  have hPrivate := untouchedActiveEdge_private_vertex_of_projectsACopies A₀ D C α β
    hOld hDifferent a
  have hij : i = j := attachment_privateStandardCarrier_unique_index
    C.toRelStructure S E.toRelStructure (fun k => (f k).toEmbedding)
    i j a.1.1 b.1.1 hPrivate hImage
  subst j
  have hab : a = b := by
    apply Subtype.ext
    apply Subtype.ext
    exact supportCarrier_image_eq_of_injective (fun x : X => Std i x)
      (Std i).toEmbedding.injective hImage
  subst b
  rfl

private theorem standardActiveEdge_pair_surjective_of_projectsACopies
    (hOld : ProjectsACopies A D C) (hCore : ProjectsACopies A D E)
    (hDifferent : α ≠ β) (hCoreSupport : ∀ y : Y, E.part y ∈ copyCarrier α) :
    Function.Surjective (fun ia : I × OldActive =>
      standardActiveEdge A C S E f β.toFunctionEmbedding ia.1 ia.2) := by
  intro a
  have hOut := projectsACopies_freeAttachment A D C S E f hA hOld hCore
  obtain ⟨b, hb⟩ := activePhysicalEdge_has_projectedCarrier_of_projectsACopies
    A₀ D Out hOut β a
  obtain ⟨i, hi⟩ := irreducibleEmbedding_has_standard_owner_of_not_core A C S E f hA b.val
    (untouchedProjectedCopy_not_core A₀ D C α β E f hDifferent hCoreSupport b)
  let old := projectedFactorThroughStandard A C S E f β.toFunctionEmbedding i b hi
  let oldEdge : OldActive := ⟨⟨copyCarrier old.val, ⟨old.val, rfl⟩⟩,
    by rintro x ⟨u, rfl⟩; exact projected_mem_activeCarrier A C β.toFunctionEmbedding old u⟩
  refine ⟨(i, oldEdge), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (fun x : X => Std i x) '' copyCarrier old.val = a.1.1
  rw [hb]
  ext z
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, hz⟩
    exact ⟨u, (projectedFactorThroughStandard_spec
      A C S E f β.toFunctionEmbedding i b hi u).symm.trans hz⟩
  · rintro ⟨u, rfl⟩
    exact ⟨old.val u, ⟨u, rfl⟩, projectedFactorThroughStandard_spec
      A C S E f β.toFunctionEmbedding i b hi u⟩

/-- The complete untouched support is indexed by the attachment copy and
its old physical edge. Only actual A-copy projections are used. -/
noncomputable def untouchedActiveEdgeEquiv_of_projectsACopies
    (hOld : ProjectsACopies A D C) (hCore : ProjectsACopies A D E)
    (hDifferent : α ≠ β) (hCoreSupport : ∀ y : Y, E.part y ∈ copyCarrier α) :
    (I × OldActive) ≃ NewActive :=
  Equiv.ofBijective (fun ia : I × OldActive =>
    standardActiveEdge A C S E f β.toFunctionEmbedding ia.1 ia.2)
    ⟨standardActiveEdge_pair_injective_of_projectsACopies A₀ D C α β E f hOld hDifferent,
      standardActiveEdge_pair_surjective_of_projectsACopies A₀ D C α β E f
        hOld hCore hDifferent hCoreSupport⟩

end EdgeEquiv

section Refinement

variable (D : RelStructure L.withOrder P)
variable (C : StructuralRamsey.Partite.System L.withOrder P X)
variable (α β : Embedding A₀.ordered D)
variable (E : StructuralRamsey.Partite.System L.withOrder P Y)
variable (f : I → StructuralRamsey.Partite.Embedding
  (C.induce (activeCarrier A₀.ordered C α.toFunctionEmbedding)) E)

local notation "S" => activeCarrier A C α.toFunctionEmbedding
local notation "Out" => StructuralRamsey.Partite.Attachment.attach C S E f
local notation "Std" => StructuralRamsey.Partite.Attachment.copyEmbedding C S E f
local notation "OldActive" =>
  SharedOldACarrierEdge A C.toRelStructure (activeCarrier A C β.toFunctionEmbedding)
local notation "NewActive" =>
  SharedOldACarrierEdge A (StructuralRamsey.Partite.System.toRelStructure Out)
    (activeCarrier A Out β.toFunctionEmbedding)

variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A₀.ordered C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A₀.ordered E.toRelStructure) m)
variable (hShared : ∀ _i : I,
  Nonempty (SharedOldACarrierEdge A₀.ordered C.toRelStructure
    (activeCarrier A₀.ordered C α.toFunctionEmbedding)))

local notation "Train" => generatedActualASupportTrain A hA C.toRelStructure S
  E.toRelStructure (fun j => StructuralRamsey.Partite.Embedding.toEmbedding (f j)) T U hShared
local notation "OldTrain" => EdgeTrainLevels.restrict T
  (sharedOldACarrierInclusion A C.toRelStructure (activeCarrier A C β.toFunctionEmbedding))
local notation "NewTrain" => EdgeTrainLevels.restrict Train
  (sharedOldACarrierInclusion A (StructuralRamsey.Partite.System.toRelStructure Out)
    (activeCarrier A Out β.toFunctionEmbedding))

/-- Attachments over a different base edge append one level to each
untouched first-wagon refinement on its complete projected support. -/
noncomputable def untouchedActiveFirstWagonRefinement_of_projectsACopies
    (hOld : ProjectsACopies A D C) (hCore : ProjectsACopies A D E)
    (hBaseLinear : ALinear A D) (hDifferent : α ≠ β)
    (hCoreSupport : ∀ y : Y, E.part y ∈ copyCarrier α)
    (hRel : ∀ (μ : Fin (m + 1)) (i : I)
      (a b : SharedOldACarrierEdge A C.toRelStructure S),
      T.rel μ a.1 b.1 ↔ U.rel μ
        (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure
          (fun j => (f j).toEmbedding) i a)
        (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure
          (fun j => (f j).toEmbedding) i b))
    (hm : 0 < m) (allowed : Fin (m + 1) → Set P)
    (hParameters : (Train).AdjacentParameters (fun edge => edge.1)
      (fun μ => (Out).part ⁻¹' allowed μ))
    (g : ℕ)
    (hLocal : LocalForestThrough (fun i => bSupportPiece A (f i).toEmbedding) g)
    (R : FirstWagonRefinement OldTrain hm (fun e : OldActive => e.1.1) C.part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩) g) :
    FirstWagonRefinement NewTrain hm (fun e : NewActive => e.1.1) (Out).part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩) g := by
  classical
  let eqv := untouchedActiveEdgeEquiv_of_projectsACopies A₀ D C α β E f
    hOld hCore hDifferent hCoreSupport
  let V := (NewTrain).restrict eqv.toEmbedding
  let std : I → X → StructuralRamsey.Partite.Attachment.Vertex S (W := Y) (I := I) :=
    fun i x => Std i x
  have hStandard : ∀ (i : I) (a b : OldActive),
      V.rel ⟨1, Nat.succ_lt_succ hm⟩ (i, a) (i, b) ↔
        (OldTrain).rel ⟨1, Nat.succ_lt_succ hm⟩ a b := by
    intro i a b
    exact standardActiveEdge_train_iff A C S E f β.toFunctionEmbedding
      hA T U hRel hShared ⟨1, Nat.succ_lt_succ hm⟩ i a b
  have hContained (i : I) (a : OldActive) :
      std i '' a.1.1 ⊆
        copyCarrier (standardActiveEmbedding A C S E f β.toFunctionEmbedding i).toEmbedding := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨x, a.2 hx⟩, rfl⟩
  have hCommon := standardActiveCarriers_inter_single_part
    A₀ D C α β E f hBaseLinear hDifferent
  let Rproduct := FirstRefinementAppend.append
    OldTrain hm (fun e : OldActive => e.1.1) C.part
    (allowed ⟨1, Nat.succ_lt_succ hm⟩) g R V hStandard
    std (fun i => (Std i).toEmbedding.injective) (Out).part
    (fun i x => (Std i).map_part x)
    (copyCarrier α ∩ copyCarrier β) hCommon.1
    (by
      intro i j hij a b z ha hb
      exact hCommon.2 i j hij ⟨hContained i a ha, hContained j b hb⟩)
    (by
      intro a b hab hFirst z hz
      have hEdges : (eqv a).1 ≠ (eqv b).1 := by
        intro h
        exact hab (eqv.injective (Subtype.ext h))
      exact (Train).firstEdgeIntersection_of_adjacent hm (fun edge => edge.1)
        (fun μ => (Out).part ⁻¹' allowed μ) hParameters
        (eqv a).1 (eqv b).1 hEdges hFirst hz)
    (by
      intro J carrier owner hOwner hCarrier
      apply untouchedSubcarriers_labelledGirth_of_localForest
        A₀ D C α β E f hBaseLinear hDifferent carrier ⟨owner, hOwner⟩ ?_ g hLocal
      intro j z hz
      obtain ⟨a, ha⟩ := hCarrier j hz
      exact hContained (owner j) a ha)
  exact FirstWagonRefinement.transport hm Rproduct eqv NewTrain
    (fun e => e.1.1) (fun _ => rfl) (fun _ _ _ => Iff.rfl)

end Refinement

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

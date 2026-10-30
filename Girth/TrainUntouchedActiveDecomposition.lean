import Girth.StandardActiveFactor
import Girth.ActiveCarrierProjectedSupport
import Girth.ForestUniqueStandardOwner
import Girth.TrainGeneratedActualAllLevelRestriction
import Girth.TrainActualPhysicalEdgeCarrierEval

set_option Elab.async false

/-!
# Complete physical support of an untouched active subsystem

An untouched fibre is not just a chosen family of projected copies.  The
refinement invariant uses every physical A-edge contained in its true active
carrier.  For finite ordered A, these are exactly the projected A-edges.

After attachment over a different base A-copy, every such output edge has
a unique standard owner.  This gives a literal equivalence between its
complete physical support and the product of the standard index type with
the old active physical support.  The map retains the whole edge carrier,
and every generated train relation restricts exactly on each standard.

Only the core's support over the processed base copy is needed to exclude
core edges.  Finiteness and distinct physical base carriers provide a
private part, even when A has just one vertex.  No output girth, linearity,
strongness, or coverage by designated copies is assumed.  Base A-linearity
is used only to bound intersections of different standard active carriers
by a single base part.  Their vertices need not be disjoint.

These are the physical decomposition and exact restriction inputs for
transporting old refinements.  Constructing the appended refinement level,
its complete labelled child-girth bound, and remaining-fibre readiness is
separate work.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X Y I : Type v}

section StandardMap

variable (A : RelStructure L UA)
variable (C : StructuralRamsey.Partite.System L P X) (S : Set X)
variable (E : StructuralRamsey.Partite.System L P Y)
variable (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
variable (β : UA ↪ P)

local notation "Out" => StructuralRamsey.Partite.Attachment.attach C S E f
local notation "Std" => StructuralRamsey.Partite.Attachment.copyEmbedding C S E f
local notation "OldActive" =>
  SharedOldACarrierEdge A C.toRelStructure (activeCarrier A C β)
local notation "NewActive" =>
  SharedOldACarrierEdge A
    (StructuralRamsey.Partite.System.toRelStructure
      (StructuralRamsey.Partite.Attachment.attach C S E f))
    (activeCarrier A (StructuralRamsey.Partite.Attachment.attach C S E f) β)

/-- Send every actual old active support edge to its full standard image.
Its output carrier is active because projected copies commute with the
partite standard embedding. -/
noncomputable def standardActiveEdge (i : I) (a : OldActive) : NewActive := by
  refine ⟨⟨(fun x : X => Std i x) '' a.1.1, ?_⟩, ?_⟩
  · obtain ⟨b, hb⟩ := a.1.2
    refine ⟨(Std i).toEmbedding.comp b, ?_⟩
    rw [copyCarrier_comp_eq_image, ← hb]
    rfl
  · rintro z ⟨x, hx, rfl⟩
    obtain ⟨b, u, hu⟩ := a.2 hx
    exact ⟨b.comp (Std i), u, congrArg (fun y : X => Std i y) hu⟩

/-- The physical carrier is the entire image; no support edges or vertices
are deleted by the active-edge map. -/
theorem standardActiveEdge_carrier (i : I) (a : OldActive) :
    (standardActiveEdge A C S E f β i a).1.1 =
      (fun x : X => Std i x) '' a.1.1 := rfl

/-- The active-edge map is exactly the existing physical standard-edge
map, so its train relations use the genuine generated attachment train. -/
theorem standardActiveEdge_eq_physical (hA : A.Irreducible)
    (i : I) (a : OldActive) :
    (standardActiveEdge A C S E f β i a).1 =
      actualAPictureEdgeEquiv A hA C.toRelStructure S E.toRelStructure
        (fun j => (f j).toEmbedding)
        (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S)
          (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure
            (fun j => (f j).toEmbedding)) i a.1) := by
  apply Subtype.ext
  exact (actualAPictureEdgeEquiv_standard_carrier A hA C.toRelStructure S
    E.toRelStructure (fun j => (f j).toEmbedding) i a.1).symm

/-- Exact restriction at every level on the complete untouched active
support of one standard.  Shared train compatibility is the usual
preservation-and-reflection premise; no new output relation is assumed. -/
theorem standardActiveEdge_train_iff (hA : A.Irreducible) {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
    (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) m)
    (hRel : ∀ (μ : Fin (m + 1)) (i : I)
      (a b : SharedOldACarrierEdge A C.toRelStructure S),
      T.rel μ a.1 b.1 ↔ U.rel μ
        (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure
          (fun j => (f j).toEmbedding) i a)
        (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure
          (fun j => (f j).toEmbedding) i b))
    (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure S))
    (μ : Fin (m + 1)) (i : I) (a b : OldActive) :
    (generatedActualASupportTrain A hA C.toRelStructure S E.toRelStructure
      (fun j => (f j).toEmbedding) T U hShared).rel μ
        (standardActiveEdge A C S E f β i a).1
        (standardActiveEdge A C S E f β i b).1 ↔ T.rel μ a.1 b.1 := by
  rw [standardActiveEdge_eq_physical A C S E f β hA,
    standardActiveEdge_eq_physical A C S E f β hA]
  exact generatedActualASupportTrain_restrict_standard A hA C.toRelStructure S
    E.toRelStructure (fun j => (f j).toEmbedding) T U hRel hShared μ i a.1 b.1

end StandardMap

section OrderedUntouched

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered
variable (D : RelStructure L.withOrder P)
variable (C : StructuralRamsey.Partite.System L.withOrder P X)
variable (α β : Embedding A₀.ordered D)
variable (E : StructuralRamsey.Partite.System L.withOrder P Y)
variable (f : I → StructuralRamsey.Partite.Embedding
  (C.induce (activeCarrier A₀.ordered C α.toFunctionEmbedding)) E)

local notation "S" => activeCarrier A C α.toFunctionEmbedding
local notation "Out" => StructuralRamsey.Partite.Attachment.attach C S E f
local notation "Std" => StructuralRamsey.Partite.Attachment.copyEmbedding C S E f
local notation "Core" => StructuralRamsey.Partite.Attachment.coreEmbedding C S E f
local notation "OldActive" =>
  SharedOldACarrierEdge A C.toRelStructure (activeCarrier A C β.toFunctionEmbedding)
local notation "NewActive" =>
  SharedOldACarrierEdge A₀.ordered
    (StructuralRamsey.Partite.System.toRelStructure
      (StructuralRamsey.Partite.Attachment.attach C S E f))
    (activeCarrier A₀.ordered (StructuralRamsey.Partite.Attachment.attach C S E f)
      β.toFunctionEmbedding)

/-- Every physical edge contained in an ordered active carrier really has
that projection.  This is about the complete support, without ambient
linearity or coverage assumptions. -/
theorem activePhysicalEdge_has_projectedCarrier
    (hPartite : C.IsPartiteOver D) (a : OldActive) :
    ∃ b : StructuralRamsey.Partite.ProjectedEmbedding A C β.toFunctionEmbedding,
      a.1.1 = copyCarrier b.val := by
  obtain ⟨b, hb⟩ := a.1.2
  obtain ⟨base, hBase⟩ := hPartite.after_irreducible_embedding
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible b
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
  have hEq : base = β := ordered_embedding_eq_of_sameCopy base β hSame
  refine ⟨⟨b, ?_⟩, hb⟩
  intro u
  exact (hBase u).symm.trans (congrArg (fun k : Embedding A D => k u) hEq)

/-- Distinct finite ordered base copies provide a private part of the
untouched fibre.  Thus every projected untouched copy has a noncore
vertex, including when A has only one vertex. -/
theorem untouchedProjectedCopy_not_core
    (hDifferent : α ≠ β)
    (hCoreSupport : ∀ y : Y, E.part y ∈ copyCarrier α)
    (a : StructuralRamsey.Partite.ProjectedEmbedding A Out β.toFunctionEmbedding) :
    ¬ copyCarrier a.val ⊆ copyCarrier (Core).toEmbedding := by
  intro hSub
  have hSame : SameCopy β α := sameCopy_of_range_subset β α (by
    intro u
    obtain ⟨y, hy⟩ := hSub (show a.val u ∈ copyCarrier a.val from ⟨u, rfl⟩)
    have hp : E.part y = β u := by
      calc
        E.part y = (Out).part (Core y) := ((Core).map_part y).symm
        _ = (Out).part (a.val u) := congrArg (Out).part hy
        _ = β u := a.property u
    have hmem := hCoreSupport y
    rw [hp] at hmem
    obtain ⟨v, hv⟩ := hmem
    exact ⟨v, hv.symm⟩)
  exact hDifferent (ordered_embedding_eq_of_sameCopy α β hSame.symm)

/-- An actual old untouched support edge has a vertex outside the processed
active carrier.  Only distinctness of the two finite ordered base copies
is required; there is no two-vertex hypothesis on A. -/
theorem untouchedActiveEdge_private_vertex
    (hPartite : C.IsPartiteOver D) (hDifferent : α ≠ β) (a : OldActive) :
    ∃ x : X, x ∈ a.1.1 ∧ x ∉ S := by
  classical
  obtain ⟨b, hb⟩ := activePhysicalEdge_has_projectedCarrier A₀ D C β hPartite a
  by_contra hNo
  have hSub : a.1.1 ⊆ S := by
    intro x hx
    by_contra hxS
    exact hNo ⟨x, hx, hxS⟩
  have hSame : SameCopy β α := sameCopy_of_range_subset β α (by
    intro u
    have hx : b.val u ∈ S := hSub (by rw [hb]; exact ⟨u, rfl⟩)
    have hp := activeCarrier_subset_support A C α.toFunctionEmbedding hx
    change C.part (b.val u) ∈ Set.range α.toFunctionEmbedding at hp
    rw [b.property u] at hp
    obtain ⟨w, hw⟩ := hp
    exact ⟨w, hw.symm⟩)
  exact hDifferent (ordered_embedding_eq_of_sameCopy α β hSame.symm)

/-- Distinct standards give distinct physical untouched support labels;
within one standard the injective vertex map recovers the old edge. -/
theorem standardActiveEdge_pair_injective
    (hPartite : C.IsPartiteOver D) (hDifferent : α ≠ β) :
    Function.Injective (fun ia : I × OldActive =>
      standardActiveEdge A C S E f β.toFunctionEmbedding ia.1 ia.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hEq
  have hImage := congrArg (fun q : NewActive => q.1.1) hEq
  have hij : i = j := attachment_privateStandardCarrier_unique_index
    C.toRelStructure S E.toRelStructure (fun k => (f k).toEmbedding)
    i j a.1.1 b.1.1
    (untouchedActiveEdge_private_vertex A₀ D C α β hPartite hDifferent a) hImage
  subst j
  have hab : a = b := by
    apply Subtype.ext
    apply Subtype.ext
    exact supportCarrier_image_eq_of_injective (fun x : X => Std i x)
      (Std i).toEmbedding.injective hImage
  cases hab
  rfl

/-- Every actual edge of the output untouched active subsystem comes from
one actual old active edge in a standard.  The core has no missing extra
untouched edges, and no edge family is pruned. -/
theorem standardActiveEdge_pair_surjective
    (hPartite : C.IsPartiteOver D) (hEPartite : E.IsPartiteOver D)
    (hDifferent : α ≠ β)
    (hCoreSupport : ∀ y : Y, E.part y ∈ copyCarrier α) :
    Function.Surjective (fun ia : I × OldActive =>
      standardActiveEdge A C S E f β.toFunctionEmbedding ia.1 ia.2) := by
  intro a
  have hOutPartite : (Out).IsPartiteOver D :=
    StructuralRamsey.Partite.Attachment.attach_isPartiteOver C S E f hPartite hEPartite
  obtain ⟨b, hb⟩ := activePhysicalEdge_has_projectedCarrier A₀ D Out β hOutPartite a
  obtain ⟨i, hi⟩ := irreducibleEmbedding_has_standard_owner_of_not_core A C S E f
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible b.val
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

/-- The complete new physical active support is literally indexed by the
standard index and the complete old physical active support.  This is the
edge-label equivalence needed to transport every old refinement partition. -/
noncomputable def untouchedActiveEdgeEquiv
    (hPartite : C.IsPartiteOver D) (hEPartite : E.IsPartiteOver D)
    (hDifferent : α ≠ β)
    (hCoreSupport : ∀ y : Y, E.part y ∈ copyCarrier α) :
    (I × OldActive) ≃ NewActive :=
  Equiv.ofBijective
    (fun ia => standardActiveEdge A C S E f β.toFunctionEmbedding ia.1 ia.2)
    ⟨standardActiveEdge_pair_injective A₀ D C α β E f hPartite hDifferent,
      standardActiveEdge_pair_surjective A₀ D C α β E f
        hPartite hEPartite hDifferent hCoreSupport⟩

omit [Finite UA] in
/-- Different standard untouched active carriers can share vertices only
over the intersection of the two physical base copies.  This does not
assert that their vertex carriers are disjoint. -/
theorem standardActiveCarriers_inter_part
    {i j : I} (hij : i ≠ j) :
    (copyCarrier (standardActiveEmbedding A C S E f β.toFunctionEmbedding i).toEmbedding ∩
      copyCarrier (standardActiveEmbedding A C S E f β.toFunctionEmbedding j).toEmbedding) ⊆
      (Out).part ⁻¹' (copyCarrier α ∩ copyCarrier β) := by
  rintro z ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  have hxy : Std i x.1 = Std j y.1 := hx.trans hy.symm
  have hp := shared_standard_copy_part_mem_base_intersection C S E f
    α.toFunctionEmbedding β.toFunctionEmbedding
    (activeCarrier_subset_support A C α.toFunctionEmbedding) hij hxy
    (activeCarrier_subset_support A C β.toFunctionEmbedding x.2)
  have hpart : (Out).part z = C.part x.1 := by
    rw [← hx]
    exact (Std i).map_part x.1
  change (Out).part z ∈ copyCarrier α ∩ copyCarrier β
  rw [hpart]
  exact hp

/-- The common base parts form a subsingleton by base A-linearity.
This supplies the geometric single-part bound, not the appended child
girth or the allowed-parameter intersection argument. -/
theorem standardActiveCarriers_inter_single_part
    (hBaseLinear : ALinear A D) (hDifferent : α ≠ β) :
    (copyCarrier α ∩ copyCarrier β).Subsingleton ∧
      ∀ i j : I, i ≠ j →
        (copyCarrier (standardActiveEmbedding A C S E f β.toFunctionEmbedding i).toEmbedding ∩
          copyCarrier (standardActiveEmbedding A C S E f β.toFunctionEmbedding j).toEmbedding) ⊆
          (Out).part ⁻¹' (copyCarrier α ∩ copyCarrier β) := by
  refine ⟨hBaseLinear α β ?_, fun _ _ hij =>
    standardActiveCarriers_inter_part A₀ D C α β E f hij⟩
  intro hSame
  exact hDifferent (ordered_embedding_eq_of_sameCopy α β hSame)

end OrderedUntouched
end StructuralRamsey.Girth

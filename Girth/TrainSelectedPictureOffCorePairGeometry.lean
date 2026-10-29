import Girth.TrainSelectedPictureWagonPairGeometry
import Girth.TrainSelectedPictureCrossStandardWagons
import Girth.TrainPictureOffCoreEdgeOwners

-- Keep dependent attachment interfaces synchronous on the pinned release
-- candidate, with ordinary kernel checking and complete diagnostics.
set_option Elab.async false

/-!
# Generated wagon uniqueness at two vertices outside the core

Every actual support edge comes from the physical core/standard edge
pushout. A core edge cannot contain a vertex outside the core, and two
different standards intersect only in the core. Consequently the edges
of any two generated wagons incident with one off-core vertex have a
common standard owner, without a localization hypothesis.

For two distinct off-core vertices, either their standard owners agree,
when old wagon linearity applies, or they differ, when the core local
piece bound forbids two different generated wagons crossing both
standards. This proves pair uniqueness for complete generated wagon
carriers outside the core. The resulting intersection and pair-edge
absorption statements assume no output linearity, output system-girth,
strongness, finiteness or endpoint localization.

Pairs with at least one vertex in the core are outside this module's
scope. In particular, the result does not assert global output wagon
linearity or global strongness of generated wagons.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section ActualAttachment

variable {L : RelLanguage.{u}} {UA X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L X) (S : Set X) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding (B.induce S) R)

local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "OldEdge" => OldACarrierEdge A B
local notation "CoreEdge" => OldACarrierEdge A R
local notation "ActualEdge" => OldACarrierEdge A (RelStructure.Attachment.attach B S R f)
local notation "Std" => RelStructure.Attachment.copyEmbedding B S R f
local notation "Core" => RelStructure.Attachment.coreEmbedding B S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A B S R f
local notation "Eqv" => actualAPictureEdgeEquiv A hA B S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  Eqv (physicalStandardEdge (sharedOldACarrierInclusion A B S) Emb i a))
local notation "CoreActual" => (fun (a : CoreEdge) =>
  Eqv (physicalCoreEdge (sharedOldACarrierInclusion A B S) I a))

/-- Arbitrary actual support edges incident with the same off-core vertex
have a common standard source. The exhaustive physical edge cover and
free attachment geometry supply the source; no wagon premise is used. -/
theorem actualASupport_offCore_incident_edges_same_standard
    (x : Vertex) (hx : x ∉ copyCarrier Core)
    (a b : ActualEdge) (hxa : x ∈ a.1) (hxb : x ∈ b.1) :
    ∃ i : I, ∃ c d : OldEdge, a = StdEdge i c ∧ b = StdEdge i d := by
  have hCover (g : ActualEdge) :
      (∃ c : CoreEdge, g = CoreActual c) ∨
        ∃ i : I, ∃ c : OldEdge, g = StdEdge i c := by
    rcases physicalPictureEdge_covered
      (sharedOldACarrierInclusion A B S) Emb ((Eqv).symm g)
      with ⟨c, hc⟩ | ⟨i, c, hc⟩
    · exact Or.inl ⟨c, ((Eqv).apply_symm_apply g).symm.trans
        (congrArg (fun p : ActualAPicturePushoutEdge A B S R I => Eqv p) hc)⟩
    · exact Or.inr ⟨i, c, ((Eqv).apply_symm_apply g).symm.trans
        (congrArg (fun p : ActualAPicturePushoutEdge A B S R I => Eqv p) hc)⟩
  have hCore (c : CoreEdge) : (CoreActual c).1 ⊆ copyCarrier Core := by
    intro z hz
    have hzImage : z ∈ (fun y : Y => Core y) '' c.1 :=
      Eq.mp (congrArg (fun Z : Set Vertex => z ∈ Z)
        (actualAPictureEdgeEquiv_core_carrier A hA B S R f c)) hz
    obtain ⟨y, _hy, hyz⟩ := hzImage
    exact ⟨y, hyz⟩
  have hStd (i : I) (c : OldEdge) : (StdEdge i c).1 ⊆ copyCarrier (Std i) := by
    intro z hz
    have hzImage : z ∈ (fun y : X => Std i y) '' c.1 :=
      Eq.mp (congrArg (fun Z : Set Vertex => z ∈ Z)
        (actualAPictureEdgeEquiv_standard_carrier A hA B S R f i c)) hz
    obtain ⟨y, _hy, hyz⟩ := hzImage
    exact ⟨y, hyz⟩
  exact picture_offCore_incident_edges_same_standard
    CoreActual StdEdge (fun g : ActualEdge => g.1)
    (fun i : I => copyCarrier (Std i)) (copyCarrier Core)
    hCover hCore hStd
    (fun _i _j hij => attachment_copy_copy_intersection_subset_core B S R f hij)
    x hx a b hxa hxb

end ActualAttachment

section SelectedAttachment

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure
  (activeCarrier A C e.toFunctionEmbedding)))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Core" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreCar" => attachedCoreAEdgeCarrier A C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S) Emb i a))
local notation "Train" => generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared
local notation "Old" => selectedPictureOrderOneData A B D C family selected T μ
local notation "Witness" => sharedWitnessOrderOneData U μ Emb CoreCar
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ

variable (hRel : ∀ (ν : Fin (m + 1)) (k : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f k p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f k q))

include hRel

/-- Two arbitrary output physical edge blocks through the same two distinct
off-core vertices have equal generated parents. Standard ownership of the
four witnessing edges is derived, rather than assumed. -/
theorem attachedSelectedPicture_offCore_blocks_parent_eq
    (hOld : (Old).LinearPretrain) (hBound : (Witness).LocalPieceSystemBound 2)
    (a b c d : ActualEdge) (x y : Vertex)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ))
    (hx : x ∉ copyCarrier Core) (hy : y ∉ copyCarrier Core) (hxy : x ≠ y)
    (ha : (Out).parent a = W₁) (hb : (Out).parent b = W₁)
    (hc : (Out).parent c = W₂) (hd : (Out).parent d = W₂)
    (hxa : x ∈ a.1) (hyb : y ∈ b.1) (hxc : x ∈ c.1) (hyd : y ∈ d.1) :
    W₁ = W₂ := by
  classical
  obtain ⟨i, a₀, c₀, rfl, rfl⟩ :=
    actualASupport_offCore_incident_edges_same_standard
      A hA C.toRelStructure S R f x hx a c hxa hxc
  obtain ⟨j, b₀, d₀, rfl, rfl⟩ :=
    actualASupport_offCore_incident_edges_same_standard
      A hA C.toRelStructure S R f y hy b d hyb hyd
  by_cases hij : i = j
  · subst j
    exact attachedSelectedPicture_same_standard_blocks_parent_eq
      A hA B D C family selected e R f T U hShared μ hRel hOld
      i a₀ b₀ c₀ d₀ x y W₁ W₂ hxy ha hb hc hd hxa hyb hxc hyd
  · exact generatedActualASupportTrain_cross_standard_wagon_unique
      A hA C.toRelStructure S R f T U hShared hRel μ hBound
      i j hij a₀ b₀ c₀ d₀ W₁ W₂ ha hb hc hd

/-- A pair of distinct off-core vertices belongs to at most one generated
output wagon. Each `WagonVertex` premise ranges over every actual incident
edge of the wagon; no source standard has been preselected. -/
theorem attachedSelectedPicture_offCore_wagon_eq_of_common_vertex_pair
    (hOld : (Old).LinearPretrain) (hBound : (Witness).LocalPieceSystemBound 2)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (x y : Vertex)
    (hx : x ∉ copyCarrier Core) (hy : y ∉ copyCarrier Core) (hxy : x ≠ y)
    (hW₁x : (Out).WagonVertex W₁ x) (hW₁y : (Out).WagonVertex W₁ y)
    (hW₂x : (Out).WagonVertex W₂ x) (hW₂y : (Out).WagonVertex W₂ y) :
    W₁ = W₂ := by
  obtain ⟨a, ha, hxa⟩ := hW₁x
  obtain ⟨b, hb, hyb⟩ := hW₁y
  obtain ⟨c, hc, hxc⟩ := hW₂x
  obtain ⟨d, hd, hyd⟩ := hW₂y
  exact attachedSelectedPicture_offCore_blocks_parent_eq
    A hA B D C family selected e R f T U hShared μ hRel hOld hBound
    a b c d x y W₁ W₂ hx hy hxy ha hb hc hd hxa hyb hxc hyd

/-- The same pair uniqueness stated directly for complete generated wagon
class carriers, retaining their actual quotient labels. -/
theorem attachedSelectedPicture_offCore_wagon_class_eq_of_common_vertex_pair
    (hOld : (Old).LinearPretrain) (hBound : (Witness).LocalPieceSystemBound 2)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (x y : Vertex)
    (hx : x ∉ copyCarrier Core) (hy : y ∉ copyCarrier Core) (hxy : x ≠ y)
    (hW₁x : x ∈ (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₁)
    (hW₁y : y ∈ (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₁)
    (hW₂x : x ∈ (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₂)
    (hW₂y : y ∈ (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₂) :
    W₁ = W₂ := by
  obtain ⟨a, ha, hxa⟩ := (Train).exists_incident_representative
    (fun a : ActualEdge => a.1) μ W₁ x hW₁x
  obtain ⟨b, hb, hyb⟩ := (Train).exists_incident_representative
    (fun a : ActualEdge => a.1) μ W₁ y hW₁y
  obtain ⟨c, hc, hxc⟩ := (Train).exists_incident_representative
    (fun a : ActualEdge => a.1) μ W₂ x hW₂x
  obtain ⟨d, hd, hyd⟩ := (Train).exists_incident_representative
    (fun a : ActualEdge => a.1) μ W₂ y hW₂y
  exact attachedSelectedPicture_offCore_blocks_parent_eq
    A hA B D C family selected e R f T U hShared μ hRel hOld hBound
    a b c d x y W₁ W₂ hx hy hxy ha hb hc hd hxa hyb hxc hyd

/-- Distinct complete generated wagon carriers have at most one common
vertex outside the core. Nothing is asserted about their intersection
inside the core. -/
theorem attachedSelectedPicture_offCore_wagon_carriers_inter_subsingleton
    (hOld : (Old).LinearPretrain) (hBound : (Witness).LocalPieceSystemBound 2)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (hW : W₁ ≠ W₂) :
    (((Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₁ ∩
      (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₂) \
      copyCarrier Core).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  exact hW (attachedSelectedPicture_offCore_wagon_class_eq_of_common_vertex_pair
    A hA B D C family selected e R f T U hShared μ hRel hOld hBound
    W₁ W₂ x y hx.2 hy.2 hxy hx.1.1 hy.1.1 hx.1.2 hy.1.2)

/-- Any ambient physical pair edge through two distinct off-core vertices
of an output wagon has that wagon's generated parent. This is restricted
pair-edge absorption; global output linearity is not a premise. -/
theorem attachedSelectedPicture_parent_eq_of_offCore_pair
    (hOld : (Old).LinearPretrain) (hBound : (Witness).LocalPieceSystemBound 2)
    (W : Quotient ((Train).wagonSetoid μ)) (g : ActualEdge) (x y : Vertex)
    (hx : x ∉ copyCarrier Core) (hy : y ∉ copyCarrier Core) (hxy : x ≠ y)
    (hWx : (Out).WagonVertex W x) (hWy : (Out).WagonVertex W y)
    (hxg : x ∈ g.1) (hyg : y ∈ g.1) :
    (Out).parent g = W := by
  exact attachedSelectedPicture_offCore_wagon_eq_of_common_vertex_pair
    A hA B D C family selected e R f T U hShared μ hRel hOld hBound
    ((Out).parent g) W x y hx hy hxy ⟨g, rfl, hxg⟩ ⟨g, rfl, hyg⟩ hWx hWy

end SelectedAttachment
end StructuralRamsey.Girth

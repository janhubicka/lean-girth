import Girth.TrainFillingOrderedSelectedArrow
import Girth.TrainFillingIndexedActualMPhysicalTrain
import Girth.TrainFillingIndexedActualRestoredParents
import Girth.TrainFillingIndexedFaithfulParentwise
import Girth.TrainFillingTemplateConstruction

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure
open StructuralRamsey.Girth.TrainRecursiveWitness (actualEdge componentTrain_same_component_iff)

universe u u' v w

variable {L : RelLanguage.{u}} {K : RelLanguage.{u'}}
variable {U A C P V X Y Base : Type v}
variable [LinearOrder U] [Finite U] [Nontrivial X]
variable {old : RelStructure L U}
variable (W : C → PrivateWagonInput V P X)
variable (small : RelStructure K A) [Nontrivial A] (R : RelStructure K X)
variable (enumerate : X ≃ U)
variable (M : RelStructure L.withOrder (Vertex W))
variable (source : (C × P) → Embedding old.ordered M)
variable (hSource : ∀ c : C, ∀ p : P, ∀ x : X,
  source (c, p) (enumerate x) = tagVertex W c ((W c).place p x))
variable (hSupport : supportCopies old.ordered M = Set.range (contractedCarrier W))
variable (hFirstLinear : ∀ c : C, ∀ p q : P, p ≠ q →
  ((W c).oldCarrier p ∩ (W c).oldCarrier q).Subsingleton)
variable (D : RelStructure L.withOrder Base)
variable (S : StructuralRamsey.Partite.System L.withOrder Base Y)
variable (family : Set (Embedding M D))
variable (selected : Set (DesignatedCopy M D S family))
variable (hOldLinear : ALinear old.ordered S.toRelStructure)
variable (hCover : ∀ x : X, ∃ a : Embedding small R, x ∈ copyCarrier a)
variable (hTemplate : ∀ c : C, (W c).templateEdges = supportCopies small R)
variable {t : List ℕ} (T : EdgeTrainLevels P t.length) (ht : 0 < t.length)
variable (train : EdgeTrainLevels (OldACarrierEdge old.ordered S.toRelStructure) t.length)

local notation "N" => S.toRelStructure

private theorem orderedSupport_linear (h : ALinear old.ordered N) :
    ∀ e f : {s : Set Y // s ∈ supportCopies old.ordered N},
      e ≠ f → (e.1 ∩ f.1).Subsingleton :=
  oldACarrier_edges_inter_subsingleton_of_aLinear old.ordered N h

local notation "hLinear" => orderedSupport_linear S hOldLinear
local notation "H" =>
  UniformFillingData.ofOrderedSupportCopies small R enumerate hLinear hCover
local notation "I" => {b : DesignatedCopy M D S family // b ∈ selected}
local notation "β" => fun i : I =>
  selectedOrderedOldEdgeEmbedding W small R enumerate hLinear hCover
    hFirstLinear M source hSource (DesignatedCopy.embedding (Subtype.val i))
local notation "physicalTrain" =>
  contractedPhysicalTrain W old.ordered M T ht hSupport hFirstLinear
local notation "filledCut" => fun j : Fin t.length =>
  TrainFilling.inheritedCutData (UniformFillingData.toTrainFilling H) train
    (fun i : I => copyCarrier (DesignatedCopy.embedding (Subtype.val i)))
    (fun (i : I) (e : UniformFillingData.OldEdge H) =>
      Set.Subset (Subtype.val e) (copyCarrier (DesignatedCopy.embedding (Subtype.val i))))
    (Fin.castSucc j)

variable (hRestriction : ∀ b ∈ selected, ∀ μ
    (a d : Embedding old.ordered M),
  train.rel μ (actualEdge (b.embedding.comp a)) (actualEdge (b.embedding.comp d)) ↔
    (contractedPhysicalTrain W old.ordered M T ht hSupport hFirstLinear).rel μ
      (actualEdge a) (actualEdge d))

/-- The restored parameter sets are the original part sets. The inserted
first parameter uses the template, and every later parameter uses the
identical part set at the corresponding shortened cut. -/
theorem orderedFilling_adjacentParameters
    {FinePart : Type v} (partX : X → FinePart) (partN : Y → FinePart)
    (allowed : Fin (t.length + 1 + 1) → Set FinePart)
    (hPlacement : ∀ (f : (H).OldEdge) (x : X), partN ((H).place f x) = partX x)
    (hFirst : ∀ a b : (H).TemplateEdge, a ≠ b →
      a.1 ∩ b.1 ⊆ partX ⁻¹' allowed (0 : Fin (t.length + 1)).succ)
    (hOld : train.AdjacentParameters (fun e => e.1)
      (fun ν => partN ⁻¹' allowed ν.succ)) :
    ((H).toTrainFilling.inheritedTrain train).AdjacentParameters (fun e => e.1)
      (fun ν => partN ⁻¹' allowed ν) := by
  apply (H).toTrainFilling.inheritedTrain_adjacentParameters train
    (fun ν => partN ⁻¹' allowed ν) _ hOld
  apply (H).first_fibre_parameter (partX ⁻¹' allowed (0 : Fin (t.length + 1)).succ) _ hFirst
  rintro f _ ⟨x, hx, rfl⟩
  change partN ((H).place f x) ∈ allowed (0 : Fin (t.length + 1)).succ
  rw [hPlacement f x]
  exact hx

include hSupport hRestriction in
private theorem orderedSelectedOldEdge_rel_iff (i : I) (μ : Fin (t.length + 1))
    (e f : C × P) :
    train.rel μ (β i e) (β i f) ↔ (contractedChoiceTrain W T ht).rel μ e f := by
  have hEdge (cp : C × P) :
      actualEdge (source cp) =
        contractedPhysicalEdgeEquiv W old.ordered M hSupport hFirstLinear cp :=
    Subtype.ext (orderedSource_copyCarrier_eq W enumerate M source hSource cp)
  have hr : train.rel μ (β i e) (β i f) ↔
      (physicalTrain).rel μ (actualEdge (source e)) (actualEdge (source f)) :=
    hRestriction i.1 i.2 μ (source e) (source f)
  rw [hEdge e, hEdge f] at hr
  exact hr.trans (contractedPhysicalTrain_rel_iff W old.ordered M T ht
    hSupport hFirstLinear μ e f)

include hSupport hRestriction in
/-- In one selected choice, every positive relation of the actual filled
train, including its top, is the original relation on first-wagon owners. -/
theorem orderedSelectedFilledEdge_rel_succ (i : I) (c : C)
    (μ : Fin (t.length + 1)) (a b : (W c).Edge) :
    ((H).toTrainFilling.inheritedTrain train).rel μ.succ
      (selectedIndexedFilledEdgeEmbedding W H hTemplate (β i) (tagEdge W c a))
      (selectedIndexedFilledEdgeEmbedding W H hTemplate (β i) (tagEdge W c b)) ↔
      T.rel μ a.1 b.1 := by
  refine ((H).toTrainFilling.inheritedTrain_rel_succ train μ _ _).trans ?_
  have ha := selectedIndexedFilledEdgeEmbedding_cover W H hTemplate (β i) (tagEdge W c a)
  have hb := selectedIndexedFilledEdgeEmbedding_cover W H hTemplate (β i) (tagEdge W c b)
  exact (Iff.of_eq (congrArg₂ (train.rel μ) ha hb)).trans
    ((orderedSelectedOldEdge_rel_iff W small R enumerate M source hSource hSupport
      hFirstLinear D S family selected hOldLinear hCover T ht train hRestriction i μ
      (c, a.1) (c, b.1)).trans (componentTrain_same_component_iff T ht c μ a.1 b.1))

include source hSource hSupport hFirstLinear hTemplate ht hRestriction in
/-- At a proper shortened cut, the genuine selected ordered embeddings
determine the vertex, filled edge, and parent maps for scattering. -/
noncomputable def orderedSelectedTailRealization (j : Fin t.length) :
    FaithfulParentwisePhysicalRealization W
      (fun p => Quotient.mk (T.wagonSetoid j.castSucc) p) (filledCut j) where
  vertex := fun i => i.1.embedding.toFunctionEmbedding
  edge := fun i => selectedIndexedFilledEdgeEmbedding W H hTemplate (β i)
  parent_surjective := by
    intro q
    induction q using Quotient.inductionOn with
    | h p => exact ⟨p, rfl⟩
  template_nonempty := by
    intro c
    obtain ⟨x, _, _⟩ := exists_pair_ne X
    obtain ⟨a, _⟩ := hCover x
    exact ⟨⟨copyCarrier a, by rw [hTemplate c]; exact ⟨a, rfl⟩⟩⟩
  edge_parent_faithful := by
    intro i a b
    exact selectedIndexedRestoredParent_iff W H hTemplate T ht train (β i)
      j.castSucc j.isLt (fun e f =>
        (orderedSelectedOldEdge_rel_iff W small R enumerate M source hSource hSupport
          hFirstLinear D S family selected hOldLinear hCover T ht train hRestriction i
          j.castSucc e f).symm) a b
  edgeCarrier_eq := by
    intro i a
    exact selectedOrderedFilling_edgeCarrier W small R enumerate hLinear hCover hTemplate
      M source hSource i.1.embedding (β i) (fun _ _ => rfl) a
  copyCarrier_eq := fun _ => rfl
  copyEdges_eq := by
    intro i
    have hRange := selectedOrderedOldEdgeEmbedding_range W small R enumerate hLinear hCover
      hFirstLinear M source hSource hSupport i.1.embedding
    exact (congrArg (fun s : Set (H).OldEdge => (H).toTrainFilling.cover ⁻¹' s) hRange.symm).trans
      (selectedIndexedFilledEdgeEmbedding_range W H hTemplate (β i)).symm

/-- Fill and scatter at every proper shortened cut, including the equality
cut. The scattered target uses all ambient filled edges and real quotient
wagons. -/
theorem orderedSelectedTail_fullSystemGirthGT
    (hLocalLinear : ALinear small R)
    (hOldGirth : ∀ j : Fin t.length,
      (selectedPictureOrderOneData old.ordered M D S family selected train
        j.castSucc).FullSystemGirthGT (t.get j))
    (j : Fin t.length) :
    ((orderedSelectedTailRealization W small R enumerate M source hSource hSupport
        hFirstLinear D S family selected hOldLinear hCover hTemplate T ht train
        hRestriction j).toParentwiseRealization.designatedFamily.target).FullSystemGirthGT
      (t.get j) := by
  apply FaithfulParentwisePhysicalRealization.target_fullSystemGirthGT
  apply (H).toTrainFilling.inheritedCutData_fullSystemGirthGT_of_fibreLinearity train
    (fun i : I => copyCarrier i.1.embedding)
    (fun i : I => {e : (H).OldEdge | e.1 ⊆ copyCarrier i.1.embedding})
    j.castSucc
  · exact hOldGirth j
  · exact (H).fibre_linear (oldACarrier_edges_inter_subsingleton_of_aLinear small R hLocalLinear)

/-- An ambient filled edge meeting the scattered target twice is an edge
of that target. Strongness of the shorter selected copy first puts its
cover in the old parent. The vertex-disjoint choice components then
identify its component, where source strongness applies. -/
theorem orderedSelectedTail_strong
    (hOldStrong : ∀ b ∈ selected, AStrong old.ordered N (copyCarrier b.embedding))
    (j : Fin t.length) (i : I) (c : C) (e : (H).toTrainFilling.NewEdge)
    (x y : Y) (hxy : x ≠ y) (hx : x ∈ e.1) (hy : y ∈ e.1) :
    let F := (orderedSelectedTailRealization W small R enumerate M source hSource hSupport
      hFirstLinear D S family selected hOldLinear hCover hTemplate T ht train
      hRestriction j).toParentwiseRealization
    x ∈ F.targetCarrier (i, c) → y ∈ F.targetCarrier (i, c) →
      e ∈ F.targetEdges (i, c) := by
  intro F hxT hyT
  have hxCopy : x ∈ copyCarrier i.1.embedding :=
    F.componentCarrier_subset_parent (i, c) (F.targetCarrier_subset_component (i, c) hxT)
  have hyCopy : y ∈ copyCarrier i.1.embedding :=
    F.componentCarrier_subset_parent (i, c) (F.targetCarrier_subset_component (i, c) hyT)
  have hSub : ((H).toTrainFilling.cover e).1 ⊆ copyCarrier i.1.embedding := by
    obtain ⟨a, ha⟩ : ((H).toTrainFilling.cover e).1 ∈ supportCopies old.ordered N :=
      ((H).toTrainFilling.cover e).2
    rw [ha]
    apply hOldStrong i.1 i.2 a
    intro hSmall
    exact hxy (hSmall ⟨ha ▸ (H).toTrainFilling.contained e hx, hxCopy⟩
      ⟨ha ▸ (H).toTrainFilling.contained e hy, hyCopy⟩)
  obtain ⟨k, hk, heK⟩ := F.old_edge_covered i e hSub
  have hkTarget : k = (i, c) := by
    by_contra hne
    exact Set.disjoint_left.mp (F.sibling_componentCarrier_disjoint k (i, c) hne hk)
      (F.edge_carrier_subset_component k e heK hx)
      (F.targetCarrier_subset_component (i, c) hxT)
  subst k
  exact (F.componentGeometry (i, c)).strong_target e heK x y hxy hx hy hxT hyT

/-- The Ramsey arrow selects a member of the same scattered family used
for the positive-cut girth bounds. -/
theorem orderedSelectedTail_ramsey
    {κ : Type w} [Nonempty (C × P)]
    (hShortArrow : ∀ colours : Embedding old.ordered N → (H).TemplateEdge → κ,
      ∃ i : I, ∀ a d : Embedding old.ordered M,
        colours (i.1.embedding.comp a) = colours (i.1.embedding.comp d))
    (hLocalArrow : ∀ word : (H).TemplateEdge → κ,
      ∃ (c : C) (colour : κ), ∀ p : P, ∀ e,
        e ∈ selectedCommonEdges W (supportCopies small R) hTemplate c p → word e = colour)
    (j : Fin t.length) (χ : (H).toTrainFilling.NewEdge → κ) :
    ∃ (i : I) (c : C) (colour : κ), ∀ e ∈
        (orderedSelectedTailRealization W small R enumerate M source hSource hSupport
          hFirstLinear D S family selected hOldLinear hCover hTemplate T ht train
          hRestriction j).toParentwiseRealization.designatedFamily.target.copyEdges (i, c),
      χ e = colour := by
  obtain ⟨i, c, colour, _, hMono⟩ :=
    selectedOrderedTargetEdges_ramsey W small R enumerate hLinear hCover hTemplate
      hFirstLinear M source hSource (fun i : I => i.1.embedding) hShortArrow hLocalArrow χ
  exact ⟨i, c, colour, hMono⟩

end StructuralRamsey.Girth.IndexedPrivateChoice

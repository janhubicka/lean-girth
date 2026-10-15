import Girth.TrainSelectedPictureTwoStandard
import Girth.TrainGeneratedActualAllLevelRestriction
import Girth.TrainActualPhysicalEdgeCarrierEval
import Girth.ActiveCarrierStrong

/-!
# Pull output block incidences back to the selected old picture

The output incidence model uses ALL actual A-support carriers as edges and
indexed images of precisely the selected old B-copies as designated labels.
An edge belongs to a designated label exactly when its whole carrier is
contained there. These incidences are not defined by a chosen old witness.

Factoring an ambient A-embedding through the standard embedding proves that
every such contained edge is the image of a genuine old edge. Exact generated
train restriction then pulls two incidences with one output wagon back to a
common old wagon. Thus the two-standard obstruction no longer assumes old
block incidences or chosen representatives of the two output wagons.

Active strongness follows from the usual partite, A-linear base and rigidity
hypotheses. Shared-train reflection is taken from the shared-subtrain embedding
interface, together with preservation; neither follows from relational
embedding alone. Output wagon linearity is never assumed. General segmentation
and cycle transfer, and identification with any deduplicated output copy index,
are not asserted here.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- A physical A-edge wholly inside the image of a set under an embedding
comes from an actual old A-edge inside that set. No irreducibility, finiteness,
strongness or chosen designated coverage is needed for this factorisation. -/
theorem oldACarrierEdge_pullback_of_subset_image
    {L : RelLanguage.{u}} {UA X Y : Type v}
    (A : RelStructure L UA) (B : RelStructure L X) (D : RelStructure L Y)
    (j : RelStructure.Embedding B D) (Z : Set X)
    (edge : OldACarrierEdge A D)
    (hSub : edge.1 ⊆ (fun x : X => j x) '' Z) :
    ∃ old : OldACarrierEdge A B, old.1 ⊆ Z ∧
      (fun x : X => j x) '' old.1 = edge.1 := by
  classical
  obtain ⟨a, ha⟩ := edge.2
  have hFactor : ∀ u : UA, ∃ x : X, a u = j x := by
    intro u
    obtain ⟨x, _hx, hEq⟩ := hSub (by rw [ha]; exact ⟨u, rfl⟩)
    exact ⟨x, hEq.symm⟩
  let b : RelStructure.Embedding A B := a.factorThroughRange j hFactor
  have hb (u : UA) : j (b u) = a u := by
    change j (Classical.choose (hFactor u)) = a u
    exact (Classical.choose_spec (hFactor u)).symm
  refine ⟨⟨copyCarrier b, ⟨b, rfl⟩⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨z, hz, hEq⟩ := hSub (by rw [ha]; exact ⟨u, rfl⟩)
    have hzb : z = b u := j.injective (hEq.trans (hb u).symm)
    exact hzb ▸ hz
  · apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨u, rfl⟩ := hx
      rw [hb u, ha]
      exact ⟨u, rfl⟩
    · intro y hy
      rw [ha] at hy
      obtain ⟨u, rfl⟩ := hy
      exact ⟨b u, ⟨u, rfl⟩, hb u⟩

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
local notation "ActualEdge" => OldACarrierEdge A (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Label" => Selected ⊕ OldEdge
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreCar" => attachedCoreAEdgeCarrier A C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S) Emb i a))
local notation "Train" => generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared
local notation "Old" => selectedPictureOrderOneData A B D C family selected T μ
local notation "Witness" => sharedWitnessOrderOneData U μ Emb CoreCar

/-- Intrinsic output incidences: all real A-edges, and indexed images of exactly
the prescribed old designated copies. Containment defines source-edge membership. -/
noncomputable def attachedSelectedPictureOrderOneData :
    OrderOneData Vertex ActualEdge (I × Selected)
      (Quotient ((Train).wagonSetoid μ)) where
  edgeCarrier := fun a => a.1
  copyCarrier := fun iq => (fun x : X => Std iq.1 x) '' copyCarrier iq.2.1.embedding
  copyEdges := fun iq => {a | a.1 ⊆
    (fun x : X => Std iq.1 x) '' copyCarrier iq.2.1.embedding}
  parent := Quotient.mk ((Train).wagonSetoid μ)

/-- The actual standard image of either a selected designated label or an edge. -/
noncomputable def attachedSelectedPictureLabel (i : I) :
    Label → (I × Selected) ⊕ ActualEdge
  | .inl q => .inl (i, q)
  | .inr a => .inr (StdEdge i a)

local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f

/-- Standard label carriers are their literal embedded old carriers. -/
theorem attachedSelectedPicture_carrier (i : I) (a : Label) :
    (Out).carrier (LabelMap i a) = (fun x : X => Std i x) '' (Old).carrier a := by
  cases a with
  | inl q => rfl
  | inr a =>
      exact actualAPictureEdgeEquiv_standard_carrier
        A hA C.toRelStructure S R f i a

/-- An ambient edge contained in a designated image is genuinely an old source
edge. The edge-label case retains equality of physical labels, not just carriers. -/
theorem attachedSelectedPicture_edges (i : I) (a : Label) (edge : ActualEdge) :
    edge ∈ (Out).edges (LabelMap i a) ↔
      ∃ old : OldEdge, old ∈ (Old).edges a ∧ StdEdge i old = edge := by
  cases a with
  | inl q =>
      change edge.1 ⊆ (fun x : X => Std i x) '' copyCarrier q.1.embedding ↔
        ∃ old : OldEdge, old.1 ⊆ copyCarrier q.1.embedding ∧ StdEdge i old = edge
      constructor
      · intro h
        obtain ⟨old, hOld, hImage⟩ := oldACarrierEdge_pullback_of_subset_image
          A C.toRelStructure (RelStructure.Attachment.attach C.toRelStructure S R f)
          (Std i) (copyCarrier q.1.embedding) edge h
        refine ⟨old, hOld, ?_⟩
        apply Subtype.ext
        exact (actualAPictureEdgeEquiv_standard_carrier
          A hA C.toRelStructure S R f i old).trans hImage
      · rintro ⟨old, hOld, rfl⟩
        rw [actualAPictureEdgeEquiv_standard_carrier]
        rintro z ⟨x, hx, rfl⟩
        exact ⟨x, hOld hx, rfl⟩
  | inr r =>
      change edge = StdEdge i r ↔
        ∃ old : OldEdge, old = r ∧ StdEdge i old = edge
      constructor
      · intro h
        exact ⟨r, rfl, h.symm⟩
      · rintro ⟨old, rfl, h⟩
        exact h.symm

/-- Output wagon incidence supplies an old edge witness; no train reflection
is needed until incidences of two different edges are compared. -/
theorem attachedSelectedPicture_meets_iff (i : I) (a : Label)
    (W : Quotient ((Train).wagonSetoid μ)) :
    (Out).Meets (LabelMap i a) W ↔
      ∃ old : OldEdge, old ∈ (Old).edges a ∧ (Out).parent (StdEdge i old) = W := by
  constructor
  · rintro ⟨edge, hEdge, hW⟩
    obtain ⟨old, hOld, rfl⟩ := (attachedSelectedPicture_edges
      A hA B D C family selected e R f T U hShared μ i a edge).mp hEdge
    exact ⟨old, hOld, hW⟩
  · rintro ⟨old, hOld, hW⟩
    exact ⟨StdEdge i old, (attachedSelectedPicture_edges
      A hA B D C family selected e R f T U hShared μ i a (StdEdge i old)).mpr
        ⟨old, hOld, rfl⟩, hW⟩

/-- Two output incidences with one wagon pull back to a single old wagon.
Both old source incidences and the representative are constructed here. -/
theorem attachedSelectedPicture_block_pullback
    (hRel : ∀ (ν : Fin (m + 1)) (k : I)
      (p q : SharedOldACarrierEdge A C.toRelStructure S),
      T.rel ν p.1 q.1 ↔ U.rel ν (Emb k p) (Emb k q))
    (i : I) (a b : Label) (W : Quotient ((Train).wagonSetoid μ))
    (ha : (Out).Meets (LabelMap i a) W) (hb : (Out).Meets (LabelMap i b) W) :
    ∃ r : OldEdge,
      (Old).Meets a ((Old).parent r) ∧ (Old).Meets b ((Old).parent r) ∧
      (Out).parent (StdEdge i r) = W := by
  obtain ⟨r, hr, hWr⟩ := (attachedSelectedPicture_meets_iff
    A hA B D C family selected e R f T U hShared μ i a W).mp ha
  obtain ⟨s, hs, hWs⟩ := (attachedSelectedPicture_meets_iff
    A hA B D C family selected e R f T U hShared μ i b W).mp hb
  have hOut : (Train).rel μ (StdEdge i s) (StdEdge i r) :=
    Quotient.exact (hWs.trans hWr.symm)
  have hOld : T.rel μ s r := (generatedActualASupportTrain_restrict_standard
    A hA C.toRelStructure S R f T U hRel hShared μ i s r).mp hOut
  exact ⟨r, ⟨r, hr, rfl⟩, ⟨s, hs, Quotient.sound hOld⟩, hWr⟩

/-- The selected two-standard obstruction directly from OUTPUT incidences
and arbitrary distinct output wagons. Old block incidences, representatives,
active strongness and the separate reflection premise of the previous theorem
are all supplied internally from the picture geometry and train-embedding data.
No output system-girth or output wagon linearity is assumed. -/
theorem attachedSelectedPicture_twoStandard_force_core_pairEdge
    (hPartite : C.IsPartiteOver D) (hBaseLinear : ALinear A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family → AStrong A D (copyCarrier b))
    (hFull : (Old).FullSystemGirthGT 2) (hCore : (Witness).FullSystemGirthGT 2)
    (hRel : ∀ (ν : Fin (m + 1)) (k : I)
      (p q : SharedOldACarrierEdge A C.toRelStructure S),
      T.rel ν p.1 q.1 ↔ U.rel ν (Emb k p) (Emb k q))
    (i j : I) (a b c d : Label) (x y : Vertex)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ))
    (hij : i ≠ j) (hxy : x ≠ y) (hW : W₁ ≠ W₂)
    (ha : (Out).Meets (LabelMap i a) W₁) (hb : (Out).Meets (LabelMap i b) W₁)
    (hc : (Out).Meets (LabelMap j c) W₂) (hd : (Out).Meets (LabelMap j d) W₂)
    (hyA : y ∈ (Out).carrier (LabelMap i a))
    (hxB : x ∈ (Out).carrier (LabelMap i b))
    (hyC : y ∈ (Out).carrier (LabelMap j c))
    (hxD : x ∈ (Out).carrier (LabelMap j d)) :
    (Witness).PairEdge x y := by
  obtain ⟨r, har, hbr, hWr⟩ := attachedSelectedPicture_block_pullback
    A hA B D C family selected e R f T U hShared μ hRel i a b W₁ ha hb
  obtain ⟨s, hcs, hds, hWs⟩ := attachedSelectedPicture_block_pullback
    A hA B D C family selected e R f T U hShared μ hRel j c d W₂ hc hd
  have hDistinct : ¬ (Train).rel μ (StdEdge i r) (StdEdge j s) := by
    intro h
    have hEq : (Out).parent (StdEdge i r) = (Out).parent (StdEdge j s) :=
      Quotient.sound h
    exact hW (hWr.symm.trans (hEq.trans hWs))
  rw [attachedSelectedPicture_carrier] at hyA hxB hyC hxD
  exact selectedPicture_twoStandard_force_core_pairEdge
    A B D C family selected T μ e R f U hA hShared hStrong
    (activeCarrier_aStrong_of_base_aLinear A D C hA hPartite hBaseLinear e hRigid)
    hFull hCore i j a b c d r s x y hij hxy har hbr hcs hds
    (fun k p q h => (hRel μ k p q).mpr h) hyA hxB hyC hxD hDistinct

end SelectedAttachment
end StructuralRamsey.Girth

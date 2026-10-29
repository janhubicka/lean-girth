import Girth.TrainSelectedPictureOffCorePairGeometry
import Girth.TrainActualStandardCoreIncidence
import Girth.TrainTwoLabelVertexProbe

set_option Elab.async false

/-!
# Pair uniqueness with one vertex outside the core

An off-core vertex supplies a common standard owner for all incident actual
support edges. At the second vertex, each edge is either already in that
standard or yields a genuine core-witness label meeting the same core wagon
as the standard. The latter label retains both the vertex and the original
generated output parent.

One foreign label is localized by the order-one bridge. Two foreign labels
are either equal, when the two-wagon obstruction identifies the parents, or
distinct, when the order-two three-occurrence probe supplies both bridges
into the common standard. Old wagon linearity then compares the two blocks.

Thus arbitrary generated output wagons sharing two distinct vertices are
equal as soon as one of these vertices lies outside the core. No genuine
core-edge representative at the other vertex is assumed. Both-core pairs
and global output wagon linearity remain separate obligations.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section OneOffCorePair

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
variable (hRel : ∀ (ν : Fin (m + 1)) (k : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f k p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f k q))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "SharedEdge" => SharedOldACarrierEdge A C.toRelStructure S
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreCar" => attachedCoreAEdgeCarrier A C.toRelStructure S R f
local notation "Eqv" => actualAPictureEdgeEquiv A hA C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  Eqv (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S) Emb i a))
local notation "CoreActual" => (fun (a : CoreEdge) =>
  Eqv (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I a))
local notation "Train" => generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared
local notation "Old" => selectedPictureOrderOneData A B D C family selected T μ
local notation "Witness" => sharedWitnessOrderOneData U μ Emb CoreCar
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Arbitrary actual support-edge blocks through two distinct vertices have
equal generated parents if the second vertex lies outside the core. The
first vertex and its incident edge representatives are unrestricted. -/
theorem attachedSelectedPicture_one_offCore_blocks_parent_eq
    (hOld : (Old).LinearPretrain) (hBound : (Witness).LocalPieceSystemBound 2)
    (a b c d : ActualEdge) (x y : Vertex)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ))
    (hy : y ∉ copyCarrier CoreEmb) (hxy : x ≠ y)
    (ha : (Out).parent a = W₁) (hb : (Out).parent b = W₁)
    (hc : (Out).parent c = W₂) (hd : (Out).parent d = W₂)
    (hxa : x ∈ a.1) (hyb : y ∈ b.1) (hxc : x ∈ c.1) (hyd : y ∈ d.1) :
    W₁ = W₂ := by
  classical
  by_cases hxCore : x ∈ copyCarrier CoreEmb
  swap
  · exact attachedSelectedPicture_offCore_blocks_parent_eq
      A hA B D C family selected e R f T U hShared μ hRel hOld hBound
      a b c d x y W₁ W₂ hxCore hy hxy ha hb hc hd hxa hyb hxc hyd
  obtain ⟨i, b₀, d₀, hbEq, hdEq⟩ := actualASupport_offCore_incident_edges_same_standard
    A hA C.toRelStructure S R f y hy b d hyb hyd
  have hb₀ : (Out).parent (StdEdge i b₀) = W₁ :=
    (congrArg (fun r : ActualEdge => (Out).parent r) hbEq).symm.trans hb
  have hd₀ : (Out).parent (StdEdge i d₀) = W₂ :=
    (congrArg (fun r : ActualEdge => (Out).parent r) hdEq).symm.trans hd
  have hyb₀ : y ∈ (StdEdge i b₀).1 :=
    Eq.mp (congrArg (fun r : ActualEdge => y ∈ r.1) hbEq) hyb
  have hyd₀ : y ∈ (StdEdge i d₀).1 :=
    Eq.mp (congrArg (fun r : ActualEdge => y ∈ r.1) hdEq) hyd
  let κ : Quotient (U.wagonSetoid μ) ↪ Quotient ((Train).wagonSetoid μ) :=
    generatedActualASupportTrain_coreWagonEmbedding
      A hA C.toRelStructure S R f T U
      (fun ν k s t h => (hRel ν k s t).mp h) hShared μ
  have coreParent (r : CoreEdge) :
      κ ((Witness).parent r) = (Out).parent (CoreActual r) := rfl
  let InHub (W : Quotient ((Train).wagonSetoid μ)) : Prop :=
    ∃ r : OldEdge, (Out).parent (StdEdge i r) = W ∧ x ∈ (StdEdge i r).1
  have standard_mem (k : I) (r : OldEdge) (hxr : x ∈ (StdEdge k r).1) :
      x ∈ copyCarrier (Std k) := by
    have hImage : x ∈ (fun z : X => Std k z) '' r.1 :=
      Eq.mp (congrArg (fun Z : Set Vertex => x ∈ Z)
        (actualAPictureEdgeEquiv_standard_carrier A hA C.toRelStructure S R f k r)) hxr
    obtain ⟨z, _hz, hzx⟩ := hImage
    exact ⟨z, hzx⟩
  have hCover (g : ActualEdge) :
      (∃ r : CoreEdge, g = CoreActual r) ∨
        ∃ j : I, ∃ r : OldEdge, g = StdEdge j r := by
    rcases physicalPictureEdge_covered
      (sharedOldACarrierInclusion A C.toRelStructure S) Emb ((Eqv).symm g)
      with ⟨r, hr⟩ | ⟨j, r, hr⟩
    · exact Or.inl ⟨r, ((Eqv).apply_symm_apply g).symm.trans
        (congrArg (fun p : ActualAPicturePushoutEdge A C.toRelStructure S R I => Eqv p) hr)⟩
    · exact Or.inr ⟨j, r, ((Eqv).apply_symm_apply g).symm.trans
        (congrArg (fun p : ActualAPicturePushoutEdge A C.toRelStructure S R I => Eqv p) hr)⟩
  -- A source away from the common standard retains a literal witness label,
  -- its actual vertex incidence, and the original output parent through κ.
  have source (g : ActualEdge) (r₀ : OldEdge)
      (W : Quotient ((Train).wagonSetoid μ))
      (hg : (Out).parent g = W) (hr₀ : (Out).parent (StdEdge i r₀) = W)
      (hxg : x ∈ g.1) :
      InHub W ∨ ∃ (F : I ⊕ CoreEdge) (p : Quotient (U.wagonSetoid μ)),
        Sum.inl i ≠ F ∧ κ p = W ∧ (Witness).Meets (.inl i) p ∧
          (Witness).Meets F p ∧ x ∈ (Witness).carrier F := by
    rcases hCover g with ⟨r, hgr⟩ | ⟨j, r, hgr⟩
    · have hr : (Out).parent (CoreActual r) = W :=
        (congrArg (fun s : ActualEdge => (Out).parent s) hgr).symm.trans hg
      have hxr : x ∈ CoreCar r :=
        Eq.mp (congrArg (fun Z : Set Vertex => x ∈ Z)
          (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f r))
          (Eq.mp (congrArg (fun s : ActualEdge => x ∈ s.1) hgr) hxg)
      have hSame : (Train).rel μ (StdEdge i r₀) (CoreActual r) :=
        Quotient.exact (s := (Train).wagonSetoid μ) (hr₀.trans hr.symm)
      obtain ⟨s, _hsOld, hsCore, _hsLocal⟩ :=
        generatedActualASupportTrain_standard_core_copy_local_incidence
          A hA C.toRelStructure S R f T U hShared hRel μ i r₀ r hSame
      exact Or.inr ⟨.inr r, (Witness).parent r, (by intro h; cases h),
        (coreParent r).trans hr,
        ⟨Emb i s, ⟨s, rfl⟩, Quotient.sound (s := U.wagonSetoid μ) hsCore⟩,
        ⟨r, rfl, rfl⟩, hxr⟩
    · have hr : (Out).parent (StdEdge j r) = W :=
        (congrArg (fun s : ActualEdge => (Out).parent s) hgr).symm.trans hg
      have hxr : x ∈ (StdEdge j r).1 :=
        Eq.mp (congrArg (fun s : ActualEdge => x ∈ s.1) hgr) hxg
      by_cases hij : i = j
      · subst j
        exact Or.inl ⟨r, hr, hxr⟩
      · have hSame : (Train).rel μ (StdEdge i r₀) (StdEdge j r) :=
          Quotient.exact (s := (Train).wagonSetoid μ) (hr₀.trans hr.symm)
        obtain ⟨p, s, t, hsOld, _htOld, hsp, htp, _hsLocal, _htLocal⟩ :=
          generatedActualASupportTrain_cross_standard_copy_local_incidence
            A hA C.toRelStructure S R f T U hShared hRel μ i j hij r₀ r hSame
        have hWp : W = κ p := by
          calc
            W = κ ((Witness).parent (Emb i s)) :=
              generatedActualASupportTrain_standard_parent_eq_coreEmbedding
                A hA C.toRelStructure S R f T U hShared hRel μ i r₀ s W hr₀ hsOld
            _ = κ p := congrArg (fun w => κ w) hsp
        exact Or.inr ⟨.inl j, p, (fun h => hij (Sum.inl.inj h)), hWp.symm,
          ⟨Emb i s, ⟨s, rfl⟩, hsp⟩, ⟨Emb j t, ⟨t, rfl⟩, htp⟩,
          activeAttached_mem_sharedWitness_of_standard_core
            A C e.toFunctionEmbedding R f U μ j x (standard_mem j r hxr) hxCore⟩
  -- A genuine shared bridge gives a standard edge at x with exactly the
  -- same generated output parent; no equality of unlabelled carriers is used.
  have bridge_to_hub (p : Quotient (U.wagonSetoid μ))
      (W : Quotient ((Train).wagonSetoid μ)) (hp : κ p = W)
      (hBridge : (Witness).Bridge (.inl i) x p) : InHub W := by
    obtain ⟨r, hr, hrp, hxr⟩ := hBridge
    change r ∈ Set.range (Emb i) at hr
    obtain ⟨s, hs⟩ := hr
    have hsp : (Witness).parent (Emb i s) = p :=
      (congrArg (fun r : CoreEdge => (Witness).parent r) hs).trans hrp
    have hxs : x ∈ CoreCar (Emb i s) :=
      Eq.mpr (congrArg (fun r : CoreEdge => x ∈ CoreCar r) hs) hxr
    have hImage : StdEdge i s.1 = CoreActual (Emb i s) :=
      congrArg
        (fun edge : ActualAPicturePushoutEdge A C.toRelStructure S R I => Eqv edge)
        (physicalStandardEdge_shared
          (sharedOldACarrierInclusion A C.toRelStructure S) Emb i s)
    have hParent : (Out).parent (StdEdge i s.1) = W :=
      (congrArg (fun edge : ActualEdge => (Out).parent edge) hImage).trans
        ((coreParent (Emb i s)).symm.trans
          ((congrArg (fun z : Quotient (U.wagonSetoid μ) => κ z) hsp).trans hp))
    have hCarrier : (StdEdge i s.1).1 = CoreCar (Emb i s) :=
      (congrArg (fun edge : ActualEdge => edge.1) hImage).trans
        (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f (Emb i s))
    exact ⟨s.1, hParent,
      Eq.mpr (congrArg (fun Z : Set Vertex => x ∈ Z) hCarrier) hxs⟩
  have hOne : (Witness).Bound := OrderOneData.bound_of_localPieceSystemBound
    Witness (fun n K hAccept hOrder => hBound n K hAccept (by omega))
  have localize (W₀ W : Quotient ((Train).wagonSetoid μ))
      (h₀ : InHub W₀) (F : I ⊕ CoreEdge) (p : Quotient (U.wagonSetoid μ))
      (hiF : Sum.inl i ≠ F) (hp : κ p = W)
      (hip : (Witness).Meets (.inl i) p) (hFp : (Witness).Meets F p)
      (hxF : x ∈ (Witness).carrier F) : InHub W := by
    obtain ⟨r, _hr, hxr⟩ := h₀
    have hxi : x ∈ (Witness).copyCarrier i :=
      activeAttached_mem_sharedWitness_of_standard_core
        A C e.toFunctionEmbedding R f U μ i x (standard_mem i r hxr) hxCore
    exact bridge_to_hub p W hp
      (OrderOneData.both_bridges Witness hOne (.inl i) F x p hiF hxi hxF hip hFp).1
  have compare (h₁ : InHub W₁) (h₂ : InHub W₂) : W₁ = W₂ := by
    obtain ⟨r, hr, hxr⟩ := h₁
    obtain ⟨s, hs, hxs⟩ := h₂
    exact attachedSelectedPicture_same_standard_blocks_parent_eq
      A hA B D C family selected e R f T U hShared μ hRel hOld
      i r b₀ s d₀ x y W₁ W₂ hxy hr hb₀ hs hd₀ hxr hyb₀ hxs hyd₀
  rcases source a b₀ W₁ ha hb₀ hxa with h₁ | ⟨F, p, hiF, hp, hip, hFp, hxF⟩
  · rcases source c d₀ W₂ hc hd₀ hxc with h₂ | ⟨G, q, hiG, hq, hiq, hGq, hxG⟩
    · exact compare h₁ h₂
    · exact compare h₁ (localize W₁ W₂ h₁ G q hiG hq hiq hGq hxG)
  · rcases source c d₀ W₂ hc hd₀ hxc with h₂ | ⟨G, q, hiG, hq, hiq, hGq, hxG⟩
    · exact compare (localize W₂ W₁ h₂ F p hiF hp hip hFp hxF) h₂
    · by_contra hW
      have hpq : p ≠ q := by
        intro h
        exact hW (hp.symm.trans ((congrArg (fun w => κ w) h).trans hq))
      have hFG : F ≠ G := by
        intro h
        subst G
        cases F with
        | inl j =>
          have hij : i ≠ j := fun h => hiF (congrArg Sum.inl h)
          exact OrderOneData.no_two_designated_meet_two_wagons
            Witness hBound i j p q hij hpq hip hiq hFp hGq
        | inr r =>
          obtain ⟨s, hs, hsp⟩ := hFp
          obtain ⟨t, ht, htq⟩ := hGq
          have hsr : s = r := hs
          have htr : t = r := ht
          subst s
          subst t
          exact hpq (hsp.symm.trans htq)
      obtain ⟨hBridgeP, hBridgeQ⟩ := OrderOneData.copy_bridges_of_two_label_vertex_probe
        Witness hBound i F G p q x hpq hiF hiG hFG hip hiq hxF hxG hFp hGq
      exact hW (compare (bridge_to_hub p W₁ hp hBridgeP)
        (bridge_to_hub q W₂ hq hBridgeQ))

/-- Two distinct common vertices determine an arbitrary generated wagon if
one of them is outside the core. All incidences quantify over the complete
actual output edge set. -/
theorem attachedSelectedPicture_one_offCore_wagon_eq_of_common_vertex_pair
    (hOld : (Old).LinearPretrain) (hBound : (Witness).LocalPieceSystemBound 2)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (x y : Vertex)
    (hy : y ∉ copyCarrier CoreEmb) (hxy : x ≠ y)
    (hW₁x : (Out).WagonVertex W₁ x) (hW₁y : (Out).WagonVertex W₁ y)
    (hW₂x : (Out).WagonVertex W₂ x) (hW₂y : (Out).WagonVertex W₂ y) :
    W₁ = W₂ := by
  obtain ⟨a, ha, hxa⟩ := hW₁x
  obtain ⟨b, hb, hyb⟩ := hW₁y
  obtain ⟨c, hc, hxc⟩ := hW₂x
  obtain ⟨d, hd, hyd⟩ := hW₂y
  exact attachedSelectedPicture_one_offCore_blocks_parent_eq
    A hA B D C family selected e R f T U hShared μ hRel hOld hBound
    a b c d x y W₁ W₂ hy hxy ha hb hc hd hxa hyb hxc hyd

/-- Pair uniqueness directly for the complete generated quotient-class
carriers, without a source representation at the core endpoint. -/
theorem attachedSelectedPicture_one_offCore_wagon_class_eq_of_common_vertex_pair
    (hOld : (Old).LinearPretrain) (hBound : (Witness).LocalPieceSystemBound 2)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (x y : Vertex)
    (hy : y ∉ copyCarrier CoreEmb) (hxy : x ≠ y)
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
  exact attachedSelectedPicture_one_offCore_blocks_parent_eq
    A hA B D C family selected e R f T U hShared μ hRel hOld hBound
    a b c d x y W₁ W₂ hy hxy ha hb hc hd hxa hyb hxc hyd

/-- Distinct complete output wagons sharing an off-core vertex can have no
other common vertex, including inside the core. -/
theorem attachedSelectedPicture_wagon_carriers_inter_subsingleton_of_offCore
    (hOld : (Old).LinearPretrain) (hBound : (Witness).LocalPieceSystemBound 2)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (hW : W₁ ≠ W₂)
    (y : Vertex) (hy : y ∉ copyCarrier CoreEmb)
    (hW₁y : y ∈ (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₁)
    (hW₂y : y ∈ (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₂) :
    ((Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₁ ∩
      (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₂).Subsingleton := by
  have unique (x : Vertex)
      (hx : x ∈ (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₁ ∩
        (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₂) : x = y := by
    by_contra hxy
    exact hW (attachedSelectedPicture_one_offCore_wagon_class_eq_of_common_vertex_pair
      A hA B D C family selected e R f T U hShared μ hRel hOld hBound
      W₁ W₂ x y hy hxy hx.1 hW₁y hx.2 hW₂y)
  intro x hx z hz
  exact (unique x hx).trans (unique z hz).symm

/-- An ambient support edge through two distinct vertices of an output wagon
belongs to that same wagon whenever one endpoint lies outside the core. -/
theorem attachedSelectedPicture_parent_eq_of_one_offCore_pair
    (hOld : (Old).LinearPretrain) (hBound : (Witness).LocalPieceSystemBound 2)
    (W : Quotient ((Train).wagonSetoid μ)) (g : ActualEdge) (x y : Vertex)
    (hy : y ∉ copyCarrier CoreEmb) (hxy : x ≠ y)
    (hWx : (Out).WagonVertex W x) (hWy : (Out).WagonVertex W y)
    (hxg : x ∈ g.1) (hyg : y ∈ g.1) :
    (Out).parent g = W := by
  exact attachedSelectedPicture_one_offCore_wagon_eq_of_common_vertex_pair
    A hA B D C family selected e R f T U hShared μ hRel hOld hBound
    ((Out).parent g) W x y hy hxy ⟨g, rfl, hxg⟩ ⟨g, rfl, hyg⟩ hWx hWy

end OneOffCorePair

end StructuralRamsey.Girth

import Girth.TrainSelectedPictureCommonStandardEndpoint
import Girth.TrainSelectedPictureWagonStrongness
import Girth.TrainSelectedPictureMixedPairGeometry
import Girth.TrainThreeLabelWagonProbe
import Girth.TrainFourLabelWagonFrame

set_option Elab.async false

/-!
# Linearity of complete generated output wagon carriers

The proof retains arbitrary actual endpoint edges and their original quotient
parents. A common standard at either endpoint already identifies the wagons.
The full pair-edge absorption theorem excludes an ambient edge through a
hypothetical distinct common pair, so both endpoints are core vertices with
no core pair edge.

Each wagon's endpoint witnesses are either in one standard, are genuinely
core-represented, or give two distinct source labels meeting one retained core
ancestor. The proof splits on a core wagon containing both endpoints. In the
anchored case it controls A3 by core wagon linearity; in the unanchored case
the absence of every such core wagon controls A3 directly. Private wagons
remain in the one-standard branch and receive no fictitious core ancestor.

The arbitrary four-label frame permits diagonal repetitions. Its source-edge
and original-parent records are occurrence-indexed. A supreme occurrence
replaces the adjacent competing wagon occurrence at its vertex boundary,
creating a common standard at that endpoint and closing the comparison.
No simultaneous replacement or minimum-segmentation argument is assumed.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section WagonLinearity

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
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "ActualEdge" => OldACarrierEdge A Actual
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

/-- Any two distinct vertices determine the original generated output wagon,
without a source-localization premise. Only old/core linearity, the witness
order-two local bound and whole-piece geometric strongness are inputs. -/
theorem attachedSelectedPicture_wagon_eq_of_common_vertex_pair
    (hOld : (Old).LinearPretrain) (hCore : (Witness).LinearPretrain)
    (hBound : (Witness).LocalPieceSystemBound 2)
    (hActive : AStrong A C.toRelStructure S)
    (hStd : ∀ i : I, AStrong A Actual (copyCarrier (Std i)))
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (x y : Vertex) (hxy : x ≠ y)
    (hW₁x : (Out).WagonVertex W₁ x) (hW₁y : (Out).WagonVertex W₁ y)
    (hW₂x : (Out).WagonVertex W₂ x) (hW₂y : (Out).WagonVertex W₂ y) :
    W₁ = W₂ := by
  classical
  by_contra hW
  have hxCore : x ∈ copyCarrier CoreEmb := by
    by_contra hx
    exact hW (attachedSelectedPicture_one_offCore_wagon_eq_of_common_vertex_pair
      A hA B D C family selected e R f T U hShared μ hRel hOld hBound
      W₁ W₂ y x hx hxy.symm hW₁y hW₁x hW₂y hW₂x)
  have hyCore : y ∈ copyCarrier CoreEmb := by
    by_contra hy
    exact hW (attachedSelectedPicture_one_offCore_wagon_eq_of_common_vertex_pair
      A hA B D C family selected e R f T U hShared μ hRel hOld hBound
      W₁ W₂ x y hy hxy hW₁x hW₁y hW₂x hW₂y)
  have hNoActual : ¬ (Out).PairEdge x y := by
    rintro ⟨g, hxg, hyg⟩
    have h₁ := attachedSelectedPicture_parent_eq_of_wagon_pair
      A hA B D C family selected e R f T U hShared μ hRel
      hOld hCore hBound hActive hStd W₁ g x y hxy hW₁x hW₁y hxg hyg
    have h₂ := attachedSelectedPicture_parent_eq_of_wagon_pair
      A hA B D C family selected e R f T U hShared μ hRel
      hOld hCore hBound hActive hStd W₂ g x y hxy hW₂x hW₂y hxg hyg
    exact hW (h₁.symm.trans h₂)
  have hNoPair : ¬ (Witness).PairEdge x y := by
    rintro ⟨r, hxr, hyr⟩
    exact hNoActual ⟨CoreActual r,
      Eq.mpr (congrArg (fun Z : Set Vertex => x ∈ Z)
        (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f r)) hxr,
      Eq.mpr (congrArg (fun Z : Set Vertex => y ∈ Z)
        (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f r)) hyr⟩
  let κ : Quotient (U.wagonSetoid μ) ↪ Quotient ((Train).wagonSetoid μ) :=
    generatedActualASupportTrain_coreWagonEmbedding
      A hA C.toRelStructure S R f T U
      (fun ν k s t h => (hRel ν k s t).mp h) hShared μ
  have coreParent (r : CoreEdge) :
      κ ((Witness).parent r) = (Out).parent (CoreActual r) := rfl
  have coreVertex (p : Quotient (U.wagonSetoid μ)) (z : Vertex)
      (hz : (Witness).WagonVertex p z) : (Out).WagonVertex (κ p) z := by
    obtain ⟨r, hr, hzr⟩ := hz
    refine ⟨CoreActual r,
      (coreParent r).symm.trans (congrArg (fun w => κ w) hr), ?_⟩
    exact Eq.mpr (congrArg (fun Z : Set Vertex => z ∈ Z)
      (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f r)) hzr
  let InStd (W : Quotient ((Train).wagonSetoid μ)) (i : I) (z : Vertex) : Prop :=
    ∃ r : OldEdge, (Out).parent (StdEdge i r) = W ∧ z ∈ (StdEdge i r).1
  have stdWitness (W : Quotient ((Train).wagonSetoid μ)) (i : I) (z : Vertex)
      (hzCore : z ∈ copyCarrier CoreEmb) (hz : InStd W i z) :
      z ∈ (Witness).copyCarrier i := by
    obtain ⟨r, _hr, hzr⟩ := hz
    have hImage : z ∈ (fun t : X => Std i t) '' r.1 :=
      Eq.mp (congrArg (fun Z : Set Vertex => z ∈ Z)
        (actualAPictureEdgeEquiv_standard_carrier A hA C.toRelStructure S R f i r)) hzr
    obtain ⟨t, _ht, htz⟩ := hImage
    exact activeAttached_mem_sharedWitness_of_standard_core
      A C e.toFunctionEmbedding R f U μ i z ⟨t, htz⟩ hzCore
  have bridgeToStd (W : Quotient ((Train).wagonSetoid μ)) (i : I) (z : Vertex)
      (p : Quotient (U.wagonSetoid μ)) (hp : κ p = W)
      (hBridge : (Witness).Bridge (.inl i) z p) : InStd W i z := by
    obtain ⟨r, hr, hrp, hzr⟩ := hBridge
    change r ∈ Set.range (Emb i) at hr
    obtain ⟨s, hs⟩ := hr
    have hsp : (Witness).parent (Emb i s) = p :=
      (congrArg (fun r : CoreEdge => (Witness).parent r) hs).trans hrp
    have hzs : z ∈ CoreCar (Emb i s) :=
      Eq.mpr (congrArg (fun r : CoreEdge => z ∈ CoreCar r) hs) hzr
    have hImage : StdEdge i s.1 = CoreActual (Emb i s) :=
      congrArg
        (fun edge : ActualAPicturePushoutEdge A C.toRelStructure S R I => Eqv edge)
        (physicalStandardEdge_shared
          (sharedOldACarrierInclusion A C.toRelStructure S) Emb i s)
    have hParent : (Out).parent (StdEdge i s.1) = W :=
      (congrArg (fun edge : ActualEdge => (Out).parent edge) hImage).trans
        ((coreParent (Emb i s)).symm.trans
          ((congrArg (fun w : Quotient (U.wagonSetoid μ) => κ w) hsp).trans hp))
    have hCarrier : (StdEdge i s.1).1 = CoreCar (Emb i s) :=
      (congrArg (fun edge : ActualEdge => edge.1) hImage).trans
        (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f (Emb i s))
    exact ⟨s.1, hParent,
      Eq.mpr (congrArg (fun Z : Set Vertex => z ∈ Z) hCarrier) hzs⟩
  have compareAt (V₁ V₂ : Quotient ((Train).wagonSetoid μ)) (z t : Vertex)
      (hzt : z ≠ t) (hV₁t : (Out).WagonVertex V₁ t) (hV₂t : (Out).WagonVertex V₂ t)
      (i : I) (h₁ : InStd V₁ i z) (h₂ : InStd V₂ i z) : V₁ = V₂ := by
    obtain ⟨a, ha, hza⟩ := h₁
    obtain ⟨b, hb, hzb⟩ := h₂
    exact attachedSelectedPicture_wagon_eq_of_common_standard_vertex
      A hA B D C family selected e R f T U hShared μ hRel hOld hBound
      V₁ V₂ i a b t z hzt.symm hV₁t hV₂t ha hb hza hzb
  -- A designated source carries an occurrence-specific original edge. No
  -- function assigns a unique output wagon to a whole standard label.
  let Split (W : Quotient ((Train).wagonSetoid μ)) : Prop :=
    ∃ (F G : I ⊕ CoreEdge) (p : Quotient (U.wagonSetoid μ)),
      F ≠ G ∧ κ p = W ∧ (Witness).Meets F p ∧ (Witness).Meets G p ∧
      x ∈ (Witness).carrier F ∧ y ∈ (Witness).carrier G ∧
      (∀ i : I, F = .inl i → InStd W i x) ∧
      (∀ i : I, G = .inl i → InStd W i y)
  have hCover (a : ActualEdge) :
      (∃ r : CoreEdge, a = CoreActual r) ∨
        ∃ i : I, ∃ r : OldEdge, a = StdEdge i r := by
    rcases physicalPictureEdge_covered
      (sharedOldACarrierInclusion A C.toRelStructure S) Emb ((Eqv).symm a)
      with ⟨r, hr⟩ | ⟨i, r, hr⟩
    · exact Or.inl ⟨r, ((Eqv).apply_symm_apply a).symm.trans
        (congrArg (fun p : ActualAPicturePushoutEdge A C.toRelStructure S R I => Eqv p) hr)⟩
    · exact Or.inr ⟨i, r, ((Eqv).apply_symm_apply a).symm.trans
        (congrArg (fun p : ActualAPicturePushoutEdge A C.toRelStructure S R I => Eqv p) hr)⟩
  have classify (W : Quotient ((Train).wagonSetoid μ))
      (hWx : (Out).WagonVertex W x) (hWy : (Out).WagonVertex W y) :
      (∃ i : I, InStd W i x ∧ InStd W i y) ∨
      (∃ p : Quotient (U.wagonSetoid μ), κ p = W ∧
        (Witness).WagonVertex p x ∧ (Witness).WagonVertex p y) ∨ Split W := by
    obtain ⟨a, ha, hxa⟩ := hWx
    obtain ⟨b, hb, hyb⟩ := hWy
    rcases hCover a with ⟨a₀, rfl⟩ | ⟨i, a₀, rfl⟩
    · have hxa₀ : x ∈ CoreCar a₀ :=
        Eq.mp (congrArg (fun Z : Set Vertex => x ∈ Z)
          (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f a₀)) hxa
      rcases hCover b with ⟨b₀, rfl⟩ | ⟨j, b₀, rfl⟩
      · have hyb₀ : y ∈ CoreCar b₀ :=
          Eq.mp (congrArg (fun Z : Set Vertex => y ∈ Z)
            (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f b₀)) hyb
        have hba : (Witness).parent b₀ = (Witness).parent a₀ :=
          κ.injective ((coreParent b₀).trans
            (hb.trans (ha.symm.trans (coreParent a₀).symm)))
        exact Or.inr (Or.inl ⟨(Witness).parent a₀, (coreParent a₀).trans ha,
          ⟨a₀, rfl, hxa₀⟩, ⟨b₀, hba, hyb₀⟩⟩)
      · have hSame : (Train).rel μ (StdEdge j b₀) (CoreActual a₀) :=
          Quotient.exact (s := (Train).wagonSetoid μ) (hb.trans ha.symm)
        obtain ⟨s, _hsOld, hsCore, _hsLocal⟩ :=
          generatedActualASupportTrain_standard_core_copy_local_incidence
            A hA C.toRelStructure S R f T U hShared hRel μ j b₀ a₀ hSame
        refine Or.inr (Or.inr ?_)
        refine ⟨.inr a₀, .inl j, (Witness).parent a₀,
          (by intro h; cases h), (coreParent a₀).trans ha,
          ⟨a₀, rfl, rfl⟩,
          ⟨Emb j s, ⟨s, rfl⟩, Quotient.sound (s := U.wagonSetoid μ) hsCore⟩,
          hxa₀, stdWitness W j y hyCore ⟨b₀, hb, hyb⟩, ?_, ?_⟩
        · intro k hk
          cases hk
        · intro k hk
          have hjk : j = k := Sum.inl.inj hk
          subst k
          exact ⟨b₀, hb, hyb⟩
    · rcases hCover b with ⟨b₀, rfl⟩ | ⟨j, b₀, rfl⟩
      · have hyb₀ : y ∈ CoreCar b₀ :=
          Eq.mp (congrArg (fun Z : Set Vertex => y ∈ Z)
            (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f b₀)) hyb
        have hSame : (Train).rel μ (StdEdge i a₀) (CoreActual b₀) :=
          Quotient.exact (s := (Train).wagonSetoid μ) (ha.trans hb.symm)
        obtain ⟨s, _hsOld, hsCore, _hsLocal⟩ :=
          generatedActualASupportTrain_standard_core_copy_local_incidence
            A hA C.toRelStructure S R f T U hShared hRel μ i a₀ b₀ hSame
        refine Or.inr (Or.inr ?_)
        refine ⟨.inl i, .inr b₀, (Witness).parent b₀,
          (by intro h; cases h), (coreParent b₀).trans hb,
          ⟨Emb i s, ⟨s, rfl⟩, Quotient.sound (s := U.wagonSetoid μ) hsCore⟩,
          ⟨b₀, rfl, rfl⟩,
          stdWitness W i x hxCore ⟨a₀, ha, hxa⟩, hyb₀, ?_, ?_⟩
        · intro k hk
          have hik : i = k := Sum.inl.inj hk
          subst k
          exact ⟨a₀, ha, hxa⟩
        · intro k hk
          cases hk
      · by_cases hij : i = j
        · subst j
          exact Or.inl ⟨i, ⟨a₀, ha, hxa⟩, ⟨b₀, hb, hyb⟩⟩
        · have hSame : (Train).rel μ (StdEdge i a₀) (StdEdge j b₀) :=
            Quotient.exact (s := (Train).wagonSetoid μ) (ha.trans hb.symm)
          obtain ⟨p, s, t, hsOld, _htOld, hsp, htp, _hsLocal, _htLocal⟩ :=
            generatedActualASupportTrain_cross_standard_copy_local_incidence
              A hA C.toRelStructure S R f T U hShared hRel μ i j hij a₀ b₀ hSame
          have hp : κ p = W := by
            have hWp : W = κ p := by
              calc
                W = κ ((Witness).parent (Emb i s)) :=
                  generatedActualASupportTrain_standard_parent_eq_coreEmbedding
                    A hA C.toRelStructure S R f T U hShared hRel μ i a₀ s W ha hsOld
                _ = κ p := congrArg (fun w => κ w) hsp
            exact hWp.symm
          refine Or.inr (Or.inr ?_)
          refine ⟨.inl i, .inl j, p, (fun h => hij (Sum.inl.inj h)), hp,
            ⟨Emb i s, ⟨s, rfl⟩, hsp⟩, ⟨Emb j t, ⟨t, rfl⟩, htp⟩,
            stdWitness W i x hxCore ⟨a₀, ha, hxa⟩,
            stdWitness W j y hyCore ⟨b₀, hb, hyb⟩, ?_, ?_⟩
          · intro k hk
            have hik : i = k := Sum.inl.inj hk
            subst k
            exact ⟨a₀, ha, hxa⟩
          · intro k hk
            have hjk : j = k := Sum.inl.inj hk
            subst k
            exact ⟨b₀, hb, hyb⟩
  have labelNe (V₁ V₂ : Quotient ((Train).wagonSetoid μ)) (hNe : V₁ ≠ V₂)
      (z t : Vertex) (hzt : z ≠ t)
      (hV₁t : (Out).WagonVertex V₁ t) (hV₂t : (Out).WagonVertex V₂ t)
      (F G : I ⊕ CoreEdge) (p q : Quotient (U.wagonSetoid μ))
      (hp : κ p = V₁) (hq : κ q = V₂)
      (hFp : (Witness).Meets F p) (hGq : (Witness).Meets G q)
      (hFSource : ∀ i : I, F = .inl i → InStd V₁ i z)
      (hGSource : ∀ i : I, G = .inl i → InStd V₂ i z) : F ≠ G := by
    intro h
    subst G
    cases F with
    | inl i =>
      exact hNe (compareAt V₁ V₂ z t hzt hV₁t hV₂t i (hFSource i rfl) (hGSource i rfl))
    | inr r =>
      have hrp := OrderOneData.parent_eq_of_edge_label_meets Witness r p hFp
      have hrq := OrderOneData.parent_eq_of_edge_label_meets Witness r q hGq
      exact hNe (hp.symm.trans
        ((congrArg (fun w => κ w) (hrp.symm.trans hrq)).trans hq))
  -- The two alternatives in hCommon are equalities of ORIGINAL output
  -- parents. The frame recovers the exact core labels through κ.injective.
  have fourCompare (V₁ V₂ : Quotient ((Train).wagonSetoid μ))
      (hs₁ : Split V₁) (hs₂ : Split V₂)
      (hV₁x : (Out).WagonVertex V₁ x) (hV₁y : (Out).WagonVertex V₁ y)
      (hV₂x : (Out).WagonVertex V₂ x) (hV₂y : (Out).WagonVertex V₂ y)
      (hCommon : ∀ r : Quotient (U.wagonSetoid μ),
        (Witness).WagonVertex r x → (Witness).WagonVertex r y →
          κ r = V₁ ∨ κ r = V₂) : V₁ = V₂ := by
    by_contra hNe
    obtain ⟨F₁, G₁, p, hF₁G₁, hp, hF₁p, hG₁p, hxF₁, hyG₁, hF₁Source, hG₁Source⟩ := hs₁
    obtain ⟨F₂, G₂, q, hF₂G₂, hq, hF₂q, hG₂q, hxF₂, hyG₂, hF₂Source, hG₂Source⟩ := hs₂
    have hpq : p ≠ q := by
      intro h
      exact hNe (hp.symm.trans ((congrArg (fun w => κ w) h).trans hq))
    let frame : (Witness).FourLabelWagonFrame := {
      a := F₁, b := G₁, c := G₂, d := F₂, p := p, q := q, x := x, y := y
      hab := hF₁G₁
      hbc := labelNe V₁ V₂ hNe y x hxy.symm hV₁x hV₂x
        G₁ G₂ p q hp hq hG₁p hG₂q hG₁Source hG₂Source
      hcd := hF₂G₂.symm
      hda := (labelNe V₁ V₂ hNe x y hxy hV₁y hV₂y
        F₁ F₂ p q hp hq hF₁p hF₂q hF₁Source hF₂Source).symm
      hpq := hpq, hxy := hxy
      haMeets := hF₁p, hbMeets := hG₁p, hcMeets := hG₂q, hdMeets := hF₂q
      haX := hxF₁, hbY := hyG₁, hcY := hyG₂, hdX := hxF₂ }
    have hCoreCommon : ∀ r : Quotient (U.wagonSetoid μ),
        (Witness).WagonVertex r x → (Witness).WagonVertex r y → r = p ∨ r = q := by
      intro r hrx hry
      rcases hCommon r hrx hry with hr | hr
      · exact Or.inl (κ.injective (hr.trans hp.symm))
      · exact Or.inr (κ.injective (hr.trans hq.symm))
    rcases OrderOneData.FourLabelWagonFrame.bridges_of_local_bound
        Witness frame hBound hNoPair hCoreCommon with
      ⟨hF₁, hb⟩ | ⟨hG₁, hb⟩ | ⟨hG₂, hb⟩ | ⟨hF₂, hb⟩
    · cases F₁ with
      | inl i => exact hNe (compareAt V₁ V₂ x y hxy hV₁y hV₂y i
          (hF₁Source i rfl) (bridgeToStd V₂ i x q hq hb))
      | inr r => exact False.elim hF₁
    · cases G₁ with
      | inl i => exact hNe (compareAt V₁ V₂ y x hxy.symm hV₁x hV₂x i
          (hG₁Source i rfl) (bridgeToStd V₂ i y q hq hb))
      | inr r => exact False.elim hG₁
    · cases G₂ with
      | inl i => exact hNe (compareAt V₁ V₂ y x hxy.symm hV₁x hV₂x i
          (bridgeToStd V₁ i y p hp hb) (hG₂Source i rfl))
      | inr r => exact False.elim hG₂
    · cases F₂ with
      | inl i => exact hNe (compareAt V₁ V₂ x y hxy hV₁y hV₂y i
          (bridgeToStd V₁ i x p hp hb) (hF₂Source i rfl))
      | inr r => exact False.elim hF₂
  have anchorSplit (q : Quotient (U.wagonSetoid μ))
      (hqx : (Witness).WagonVertex q x) (hqy : (Witness).WagonVertex q y) : Split (κ q) := by
    obtain ⟨a, ha, hxa⟩ := hqx
    obtain ⟨b, hb, hyb⟩ := hqy
    have hab : a ≠ b := by
      intro h
      subst b
      exact hNoPair ⟨a, hxa, hyb⟩
    refine ⟨.inr a, .inr b, q, (fun h => hab (Sum.inr.inj h)), rfl,
      ⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩, hxa, hyb, ?_, ?_⟩
    · intro i hi
      cases hi
    · intro i hi
      cases hi
  have anchoredCompare (V : Quotient ((Train).wagonSetoid μ))
      (hVx : (Out).WagonVertex V x) (hVy : (Out).WagonVertex V y)
      (q : Quotient (U.wagonSetoid μ))
      (hqx : (Witness).WagonVertex q x) (hqy : (Witness).WagonVertex q y) : V = κ q := by
    rcases classify V hVx hVy with ⟨i, hix, hiy⟩ | ⟨p, hp, hpx, hpy⟩ | hSplit
    · obtain ⟨s, _t, hsq, _htq, hxs, _hyt⟩ :=
        sharedWitness_copy_wagon_pair_shared_edges U μ Emb CoreCar hCore hBound
          i q x y hxy (stdWitness V i x hxCore hix) (stdWitness V i y hyCore hiy)
          hqx hqy hNoPair
      have hBridge : (Witness).Bridge (.inl i) x q :=
        ⟨Emb i s, ⟨s, rfl⟩, hsq, hxs⟩
      exact compareAt V (κ q) x y hxy hVy (coreVertex q y hqy) i
        hix (bridgeToStd (κ q) i x q rfl hBridge)
    · have hpq := OrderOneData.wagon_eq_of_common_vertex_pair
        Witness hCore p q x y hpx hpy hqx hqy hxy
      exact hp.symm.trans (congrArg (fun w => κ w) hpq)
    · apply fourCompare V (κ q) hSplit (anchorSplit q hqx hqy)
        hVx hVy (coreVertex q x hqx) (coreVertex q y hqy)
      intro r hrx hry
      exact Or.inr (congrArg (fun w => κ w)
        (OrderOneData.wagon_eq_of_common_vertex_pair
          Witness hCore r q x y hrx hry hqx hqy hxy))
  by_cases hAnchor : ∃ q : Quotient (U.wagonSetoid μ),
      (Witness).WagonVertex q x ∧ (Witness).WagonVertex q y
  · obtain ⟨q, hqx, hqy⟩ := hAnchor
    exact hW ((anchoredCompare W₁ hW₁x hW₁y q hqx hqy).trans
      (anchoredCompare W₂ hW₂x hW₂y q hqx hqy).symm)
  have hNoCommon (q : Quotient (U.wagonSetoid μ)) :
      ¬ ((Witness).WagonVertex q x ∧ (Witness).WagonVertex q y) :=
    fun h => hAnchor ⟨q, h⟩
  have sourceNoCore (V : Quotient ((Train).wagonSetoid μ))
      (hVx : (Out).WagonVertex V x) (hVy : (Out).WagonVertex V y) :
      (∃ i : I, InStd V i x ∧ InStd V i y) ∨ Split V := by
    rcases classify V hVx hVy with hOne | ⟨p, _hp, hpx, hpy⟩ | hSplit
    · exact Or.inl hOne
    · exact False.elim (hNoCommon p ⟨hpx, hpy⟩)
    · exact Or.inr hSplit
  have oneSplitImpossible (V₁ V₂ : Quotient ((Train).wagonSetoid μ)) (hNe : V₁ ≠ V₂)
      (hV₁x : (Out).WagonVertex V₁ x) (hV₁y : (Out).WagonVertex V₁ y)
      (hV₂x : (Out).WagonVertex V₂ x) (hV₂y : (Out).WagonVertex V₂ y)
      (hOne : ∃ i : I, InStd V₁ i x ∧ InStd V₁ i y) (hSplit : Split V₂) : False := by
    obtain ⟨i, hix, hiy⟩ := hOne
    obtain ⟨F, G, p, hFG, _hp, hFp, hGp, hxF, hyG, hFSource, hGSource⟩ := hSplit
    have hiF : Sum.inl i ≠ F := by
      intro h
      exact hNe (compareAt V₁ V₂ x y hxy hV₁y hV₂y i hix (hFSource i h.symm))
    have hiG : Sum.inl i ≠ G := by
      intro h
      exact hNe (compareAt V₁ V₂ y x hxy.symm hV₁x hV₂x i hiy (hGSource i h.symm))
    obtain ⟨r, hrx, hry⟩ := OrderOneData.common_wagon_of_three_label_wagon_probe
      Witness hBound i F G p x y hxy hiF hiG hFG
      (stdWitness V₁ i x hxCore hix) (stdWitness V₁ i y hyCore hiy) hxF hyG hFp hGp
    exact hNoCommon r ⟨hrx, hry⟩
  rcases sourceNoCore W₁ hW₁x hW₁y with ⟨i, hix, hiy⟩ | hs₁
  · rcases sourceNoCore W₂ hW₂x hW₂y with ⟨j, hjx, hjy⟩ | hs₂
    · by_cases hij : i = j
      · subst j
        exact hW (compareAt W₁ W₂ x y hxy hW₁y hW₂y i hix hjx)
      · obtain ⟨r, hrx, hry⟩ := OrderOneData.common_wagon_of_two_copy_vertex_pair
          Witness hBound i j x y hij hxy
          (stdWitness W₁ i x hxCore hix) (stdWitness W₁ i y hyCore hiy)
          (stdWitness W₂ j x hxCore hjx) (stdWitness W₂ j y hyCore hjy)
        exact hNoCommon r ⟨hrx, hry⟩
    · exact oneSplitImpossible W₁ W₂ hW hW₁x hW₁y hW₂x hW₂y ⟨i, hix, hiy⟩ hs₂
  · rcases sourceNoCore W₂ hW₂x hW₂y with hOne | hs₂
    · exact oneSplitImpossible W₂ W₁ (fun h => hW h.symm) hW₂x hW₂y hW₁x hW₁y hOne hs₁
    · apply hW
      apply fourCompare W₁ W₂ hs₁ hs₂ hW₁x hW₁y hW₂x hW₂y
      intro r hrx hry
      exact False.elim (hNoCommon r ⟨hrx, hry⟩)

/-- The same unrestricted pair comparison for complete quotient-class
carriers, retaining the generated wagon labels themselves. -/
theorem attachedSelectedPicture_wagon_class_eq_of_common_vertex_pair
    (hOld : (Old).LinearPretrain) (hCore : (Witness).LinearPretrain)
    (hBound : (Witness).LocalPieceSystemBound 2)
    (hActive : AStrong A C.toRelStructure S)
    (hStd : ∀ i : I, AStrong A Actual (copyCarrier (Std i)))
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (x y : Vertex) (hxy : x ≠ y)
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
  exact attachedSelectedPicture_wagon_eq_of_common_vertex_pair
    A hA B D C family selected e R f T U hShared μ hRel hOld hCore hBound hActive hStd
    W₁ W₂ x y hxy ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩ ⟨c, hc, hxc⟩ ⟨d, hd, hyd⟩

/-- Distinct complete generated output wagon carriers meet in at most one
vertex. There is no restriction on whether that vertex lies in the core. -/
theorem attachedSelectedPicture_wagon_carriers_inter_subsingleton
    (hOld : (Old).LinearPretrain) (hCore : (Witness).LinearPretrain)
    (hBound : (Witness).LocalPieceSystemBound 2)
    (hActive : AStrong A C.toRelStructure S)
    (hStd : ∀ i : I, AStrong A Actual (copyCarrier (Std i)))
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (hW : W₁ ≠ W₂) :
    ((Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₁ ∩
      (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W₂).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  exact hW (attachedSelectedPicture_wagon_class_eq_of_common_vertex_pair
    A hA B D C family selected e R f T U hShared μ hRel hOld hCore hBound hActive hStd
    W₁ W₂ x y hxy hx.1 hy.1 hx.2 hy.2)

/-- The wagon-carrier component of output LinearPretrain, in its exact
WagonVertex formulation. The independent ambient-edge component is separate. -/
theorem attachedSelectedPicture_wagon_vertices_inter_subsingleton
    (hOld : (Old).LinearPretrain) (hCore : (Witness).LinearPretrain)
    (hBound : (Witness).LocalPieceSystemBound 2)
    (hActive : AStrong A C.toRelStructure S)
    (hStd : ∀ i : I, AStrong A Actual (copyCarrier (Std i)))
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ)) (hW : W₁ ≠ W₂) :
    ({z : Vertex | (Out).WagonVertex W₁ z} ∩
      {z : Vertex | (Out).WagonVertex W₂ z}).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  exact hW (attachedSelectedPicture_wagon_eq_of_common_vertex_pair
    A hA B D C family selected e R f T U hShared μ hRel hOld hCore hBound hActive hStd
    W₁ W₂ x y hxy hx.1 hy.1 hx.2 hy.2)

end WagonLinearity

end StructuralRamsey.Girth


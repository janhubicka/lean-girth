import Girth.TrainSelectedPictureOneOffCorePairGeometry
import Girth.TrainSelectedPictureCorePairGeometry
import Girth.TrainPairEdgeWagonProbe

set_option Elab.async false

/-!
# Strongness of complete generated output wagons

An arbitrary ambient support edge through two distinct vertices of a generated
output wagon has that wagon's original quotient parent. The one-off-core case
is already checked. For a core/core pair, active strongness puts the pair edge
in the core, while its two wagon witnesses retain their genuine source labels.

Equal source pieces use source wagon linearity and whole-piece strongness.
Different source pieces determine one core ancestor p, with its output label
preserved. If the pair edge had a different parent, core wagon linearity would
exclude simultaneous incidence of both endpoints with p. This is exactly the
missing-incidence condition that makes the pair-edge three-occurrence probe
acceptable. Its supreme designated source acquires a shared edge through the
opposite endpoint. Both wagon witnesses then lie in one whole strong standard.

The source old/core linearity and geometric strongness inputs are explicit.
No generated output linearity, output system-girth, or global replacement
legality is assumed. Pair uniqueness without an ambient pair edge remains a
separate obligation.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section WagonStrongness

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

/-- An arbitrary ambient physical support edge through two distinct vertices
of a generated wagon has that wagon's parent. Only source old/core linearity,
the witness order-two local bound, and whole-piece geometric strongness are
assumed; generated output wagon linearity is not an input. -/
theorem attachedSelectedPicture_parent_eq_of_wagon_pair
    (hOld : (Old).LinearPretrain) (hCore : (Witness).LinearPretrain)
    (hBound : (Witness).LocalPieceSystemBound 2)
    (hActive : AStrong A C.toRelStructure S)
    (hStd : ∀ i : I, AStrong A Actual (copyCarrier (Std i)))
    (W : Quotient ((Train).wagonSetoid μ)) (g : ActualEdge) (x y : Vertex)
    (hxy : x ≠ y) (hWx : (Out).WagonVertex W x) (hWy : (Out).WagonVertex W y)
    (hxg : x ∈ g.1) (hyg : y ∈ g.1) :
    (Out).parent g = W := by
  classical
  by_cases hxCore : x ∈ copyCarrier CoreEmb
  swap
  · exact attachedSelectedPicture_parent_eq_of_one_offCore_pair
      A hA B D C family selected e R f T U hShared μ hRel hOld hBound
      W g y x hxCore hxy.symm hWy hWx hyg hxg
  by_cases hyCore : y ∈ copyCarrier CoreEmb
  swap
  · exact attachedSelectedPicture_parent_eq_of_one_offCore_pair
      A hA B D C family selected e R f T U hShared μ hRel hOld hBound
      W g x y hyCore hxy hWx hWy hxg hyg
  have hCoreStrong : AStrong A Actual (copyCarrier CoreEmb) :=
    attachment_core_aStrong C.toRelStructure S R f hA hActive
  have hgSub : g.1 ⊆ copyCarrier CoreEmb :=
    oldACarrier_subset_of_two_mem_aStrong A Actual (copyCarrier CoreEmb)
      hCoreStrong g x y hxy hxg hyg hxCore hyCore
  obtain ⟨g₀, hg₀⟩ := actualASupport_core_edge_pullback
    A hA C.toRelStructure S R f g hgSub
  let κ : Quotient (U.wagonSetoid μ) ↪ Quotient ((Train).wagonSetoid μ) :=
    generatedActualASupportTrain_coreWagonEmbedding
      A hA C.toRelStructure S R f T U
      (fun ν k s t h => (hRel ν k s t).mp h) hShared μ
  have coreParent (r : CoreEdge) :
      κ ((Witness).parent r) = (Out).parent (CoreActual r) := rfl
  have hgParent : κ ((Witness).parent g₀) = (Out).parent g :=
    (coreParent g₀).trans (congrArg (fun r : ActualEdge => (Out).parent r) hg₀)
  have hgCarrier : CoreCar g₀ = g.1 :=
    (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f g₀).symm.trans
      (congrArg (fun r : ActualEdge => r.1) hg₀)
  have hxg₀ : x ∈ CoreCar g₀ :=
    Eq.mpr (congrArg (fun Z : Set Vertex => x ∈ Z) hgCarrier) hxg
  have hyg₀ : y ∈ CoreCar g₀ :=
    Eq.mpr (congrArg (fun Z : Set Vertex => y ∈ Z) hgCarrier) hyg
  have stdSub (i : I) (r : OldEdge) : (StdEdge i r).1 ⊆ copyCarrier (Std i) := by
    intro z hz
    have hImage : z ∈ (fun t : X => Std i t) '' r.1 :=
      Eq.mp (congrArg (fun Z : Set Vertex => z ∈ Z)
        (actualAPictureEdgeEquiv_standard_carrier A hA C.toRelStructure S R f i r)) hz
    obtain ⟨t, _ht, htz⟩ := hImage
    exact ⟨t, htz⟩
  have coreSub (r : CoreEdge) : (CoreActual r).1 ⊆ copyCarrier CoreEmb := by
    intro z hz
    have hImage : z ∈ CoreCar r :=
      Eq.mp (congrArg (fun Z : Set Vertex => z ∈ Z)
        (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f r)) hz
    obtain ⟨t, _ht, htz⟩ := hImage
    exact ⟨t, htz⟩
  let InStd (i : I) (z : Vertex) : Prop :=
    ∃ r : OldEdge, (Out).parent (StdEdge i r) = W ∧ z ∈ (StdEdge i r).1
  have stdAbsorb (i : I) (hx : InStd i x) (hy : InStd i y) :
      (Out).parent g = W := by
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    exact attachedSelectedPicture_parent_eq_of_standard_pair
      A hA B D C family selected e R f T U hShared μ hRel hOld
      i (hStd i) (StdEdge i a) (StdEdge i b) g x y W hxy
      (stdSub i a) (stdSub i b) ha hb hxa hyb hxg hyg
  have bridgeToStd (i : I) (z : Vertex) (p : Quotient (U.wagonSetoid μ))
      (hp : κ p = W) (hBridge : (Witness).Bridge (.inl i) z p) : InStd i z := by
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
  -- The pair edge is present. Its different parent, together with source
  -- core linearity, supplies the missing-incidence hypothesis for A2.
  have probeCase (F G : I ⊕ CoreEdge) (p : Quotient (U.wagonSetoid μ))
      (hFG : F ≠ G) (hp : κ p = W)
      (hFp : (Witness).Meets F p) (hGp : (Witness).Meets G p)
      (hxF : x ∈ (Witness).carrier F) (hyG : y ∈ (Witness).carrier G)
      (hFSource : ∀ i : I, F = .inl i → InStd i x)
      (hGSource : ∀ i : I, G = .inl i → InStd i y) :
      (Out).parent g = W := by
    by_contra hNe
    have hCoreNe : (Witness).parent g₀ ≠ p := by
      intro h
      exact hNe (hgParent.symm.trans ((congrArg (fun w => κ w) h).trans hp))
    have edgeDifferent (F : I ⊕ CoreEdge) (hFp : (Witness).Meets F p) :
        Sum.inr g₀ ≠ F := by
      intro h
      have hm : (Witness).Meets (.inr g₀) p :=
        Eq.mpr (congrArg (fun lab : I ⊕ CoreEdge => (Witness).Meets lab p) h) hFp
      obtain ⟨r, hr, hrp⟩ := hm
      have hrg : r = g₀ := hr
      exact hCoreNe ((congrArg (fun r : CoreEdge => (Witness).parent r) hrg).symm.trans hrp)
    have hMissing : ¬ ((Witness).WagonVertex p x ∧ (Witness).WagonVertex p y) := by
      intro hBoth
      exact hCoreNe (OrderOneData.parent_eq_of_two_vertices_in_wagon
        Witness hCore g₀ p x y hxg₀ hyg₀ hBoth.1 hBoth.2 hxy)
    rcases OrderOneData.twoLabel_wagon_bridge_of_pair_edge
        Witness hBound g₀ F G p x y hxy hFG
        (edgeDifferent F hFp) (edgeDifferent G hGp)
        hxg₀ hyg₀ hxF hyG hFp hGp hMissing with ⟨hF, hb⟩ | ⟨hG, hb⟩
    · cases F with
      | inl i => exact hNe (stdAbsorb i (hFSource i rfl) (bridgeToStd i y p hp hb))
      | inr r => exact False.elim hF
    · cases G with
      | inl i => exact hNe (stdAbsorb i (bridgeToStd i x p hp hb) (hGSource i rfl))
      | inr r => exact False.elim hG
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
  obtain ⟨a, ha, hxa⟩ := hWx
  obtain ⟨b, hb, hyb⟩ := hWy
  rcases hCover a with ⟨a₀, rfl⟩ | ⟨i, a₀, rfl⟩
  · rcases hCover b with ⟨b₀, rfl⟩ | ⟨j, b₀, rfl⟩
    · exact generatedActualASupportTrain_parent_eq_of_core_pair
        A hA C.toRelStructure S R f T U hShared
        (fun ν k s t h => (hRel ν k s t).mp h) μ hActive hCore
        (CoreActual a₀) (CoreActual b₀) g W x y hxy
        (coreSub a₀) (coreSub b₀) ha hb hxa hyb hxg hyg
    · have hSame : (Train).rel μ (StdEdge j b₀) (CoreActual a₀) :=
        Quotient.exact (s := (Train).wagonSetoid μ) (hb.trans ha.symm)
      obtain ⟨s, _hsOld, hsCore, _hsLocal⟩ :=
        generatedActualASupportTrain_standard_core_copy_local_incidence
          A hA C.toRelStructure S R f T U hShared hRel μ j b₀ a₀ hSame
      have hxa₀ : x ∈ CoreCar a₀ :=
        Eq.mp (congrArg (fun Z : Set Vertex => x ∈ Z)
          (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f a₀)) hxa
      refine probeCase (.inr a₀) (.inl j) ((Witness).parent a₀)
        (by intro h; cases h) ((coreParent a₀).trans ha)
        ⟨a₀, rfl, rfl⟩
        ⟨Emb j s, ⟨s, rfl⟩, Quotient.sound (s := U.wagonSetoid μ) hsCore⟩
        hxa₀
        (activeAttached_mem_sharedWitness_of_standard_core
          A C e.toFunctionEmbedding R f U μ j y (stdSub j b₀ hyb) hyCore) ?_ ?_
      · intro k hk
        cases hk
      · intro k hk
        have hjk : j = k := Sum.inl.inj hk
        subst k
        exact ⟨b₀, hb, hyb⟩
  · rcases hCover b with ⟨b₀, rfl⟩ | ⟨j, b₀, rfl⟩
    · have hSame : (Train).rel μ (StdEdge i a₀) (CoreActual b₀) :=
        Quotient.exact (s := (Train).wagonSetoid μ) (ha.trans hb.symm)
      obtain ⟨s, _hsOld, hsCore, _hsLocal⟩ :=
        generatedActualASupportTrain_standard_core_copy_local_incidence
          A hA C.toRelStructure S R f T U hShared hRel μ i a₀ b₀ hSame
      have hyb₀ : y ∈ CoreCar b₀ :=
        Eq.mp (congrArg (fun Z : Set Vertex => y ∈ Z)
          (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f b₀)) hyb
      refine probeCase (.inl i) (.inr b₀) ((Witness).parent b₀)
        (by intro h; cases h) ((coreParent b₀).trans hb)
        ⟨Emb i s, ⟨s, rfl⟩, Quotient.sound (s := U.wagonSetoid μ) hsCore⟩
        ⟨b₀, rfl, rfl⟩
        (activeAttached_mem_sharedWitness_of_standard_core
          A C e.toFunctionEmbedding R f U μ i x (stdSub i a₀ hxa) hxCore)
        hyb₀ ?_ ?_
      · intro k hk
        have hik : i = k := Sum.inl.inj hk
        subst k
        exact ⟨a₀, ha, hxa⟩
      · intro k hk
        cases hk
    · by_cases hij : i = j
      · subst j
        exact stdAbsorb i ⟨a₀, ha, hxa⟩ ⟨b₀, hb, hyb⟩
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
        refine probeCase (.inl i) (.inl j) p
          (fun h => hij (Sum.inl.inj h)) hp
          ⟨Emb i s, ⟨s, rfl⟩, hsp⟩ ⟨Emb j t, ⟨t, rfl⟩, htp⟩
          (activeAttached_mem_sharedWitness_of_standard_core
            A C e.toFunctionEmbedding R f U μ i x (stdSub i a₀ hxa) hxCore)
          (activeAttached_mem_sharedWitness_of_standard_core
            A C e.toFunctionEmbedding R f U μ j y (stdSub j b₀ hyb) hyCore) ?_ ?_
        · intro k hk
          have hik : i = k := Sum.inl.inj hk
          subst k
          exact ⟨a₀, ha, hxa⟩
        · intro k hk
          have hjk : j = k := Sum.inl.inj hk
          subst k
          exact ⟨b₀, hb, hyb⟩

/-- An actual support edge with a different generated parent meets the
complete carrier of an output wagon in at most one vertex. -/
theorem attachedSelectedPicture_outside_edge_wagon_inter_subsingleton
    (hOld : (Old).LinearPretrain) (hCore : (Witness).LinearPretrain)
    (hBound : (Witness).LocalPieceSystemBound 2)
    (hActive : AStrong A C.toRelStructure S)
    (hStd : ∀ i : I, AStrong A Actual (copyCarrier (Std i)))
    (W : Quotient ((Train).wagonSetoid μ)) (g : ActualEdge)
    (hNe : (Out).parent g ≠ W) :
    (g.1 ∩ (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  obtain ⟨a, ha, hxa⟩ := (Train).exists_incident_representative
    (fun a : ActualEdge => a.1) μ W x hx.2
  obtain ⟨b, hb, hyb⟩ := (Train).exists_incident_representative
    (fun a : ActualEdge => a.1) μ W y hy.2
  exact hNe (attachedSelectedPicture_parent_eq_of_wagon_pair
    A hA B D C family selected e R f T U hShared μ hRel hOld hCore hBound hActive hStd
    W g x y hxy ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩ hx.1 hy.1)

/-- Every complete generated output wagon carrier is A-strong in the entire
actual attachment. This is the existing relational AStrong predicate,
obtained from the stronger parent-preserving pair-edge absorption theorem. -/
theorem attachedSelectedPicture_wagon_aStrong
    (hOld : (Old).LinearPretrain) (hCore : (Witness).LinearPretrain)
    (hBound : (Witness).LocalPieceSystemBound 2)
    (hActive : AStrong A C.toRelStructure S)
    (hStd : ∀ i : I, AStrong A Actual (copyCarrier (Std i)))
    (W : Quotient ((Train).wagonSetoid μ)) :
    AStrong A Actual ((Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W) := by
  classical
  intro r hMeet
  let g : ActualEdge := ⟨copyCarrier r, ⟨r, rfl⟩⟩
  have hg : (Out).parent g = W := by
    by_contra hNe
    exact hMeet (attachedSelectedPicture_outside_edge_wagon_inter_subsingleton
      A hA B D C family selected e R f T U hShared μ hRel hOld hCore hBound hActive hStd
      W g hNe)
  intro z hz
  have hzOwn : z ∈ (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ
      ((Out).parent g) :=
    (Train).mem_wagonClassCarrier_of_mem_edge (fun a : ActualEdge => a.1) μ g z hz
  exact Eq.mp (congrArg
    (fun w : Quotient ((Train).wagonSetoid μ) =>
      z ∈ (Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ w) hg) hzOwn

end WagonStrongness

end StructuralRamsey.Girth

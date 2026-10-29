import Girth.TrainSelectedPictureOffCorePairGeometry
import Girth.TrainActualStandardCoreIncidence
import Girth.TrainTwoWagonVertexProbe

set_option Elab.async false

/-!
# A core-represented common vertex and an off-core common vertex

Two generated output wagons have genuine core-edge witnesses at a common
vertex x and arbitrary actual edge witnesses at a common off-core vertex y.
The off-core edge witnesses have a common standard owner i. Exact generated
standard/core incidence shows that witness copy i meets both original core
wagon classes.

If the output parents differed, so would their core classes. The order-two
two-wagon vertex probe then supplies a shared edge of each class through x
inside copy i. These shared edges retain their original output parents.
Together with the old edges through y they form two standard-local blocks,
so old wagon linearity identifies the two output parents.

Core linearity, strongness, and output linearity are not assumptions. The
genuine core witnesses through x remain explicit; this does not localize
arbitrary output wagon incidences at core vertices.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section CoreOffCorePair

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
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreCar" => attachedCoreAEdgeCarrier A C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S) Emb i a))
local notation "CoreActual" => (fun (a : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I a))
local notation "Train" => generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared
local notation "Old" => selectedPictureOrderOneData A B D C family selected T μ
local notation "Witness" => sharedWitnessOrderOneData U μ Emb CoreCar
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Output wagons sharing a genuinely core-represented vertex and an off-core
vertex have equal parents. Only the old linearity and the core order-two
local piece bound are needed; source core linearity is not required. -/
theorem attachedSelectedPicture_core_offCore_blocks_parent_eq
    (hOld : (Old).LinearPretrain) (hBound : (Witness).LocalPieceSystemBound 2)
    (a : CoreEdge) (b : ActualEdge) (c : CoreEdge) (d : ActualEdge)
    (x y : Vertex) (W₁ W₂ : Quotient ((Train).wagonSetoid μ))
    (hy : y ∉ copyCarrier CoreEmb)
    (ha : (Out).parent (CoreActual a) = W₁) (hb : (Out).parent b = W₁)
    (hc : (Out).parent (CoreActual c) = W₂) (hd : (Out).parent d = W₂)
    (hxa : x ∈ (CoreActual a).1) (hyb : y ∈ b.1)
    (hxc : x ∈ (CoreActual c).1) (hyd : y ∈ d.1) :
    W₁ = W₂ := by
  classical
  let preserve := fun (ν : Fin (m + 1)) (k : I)
    (s t : SharedEdge) => (hRel ν k s t).mp
  let κ : Quotient (U.wagonSetoid μ) ↪ Quotient ((Train).wagonSetoid μ) :=
    generatedActualASupportTrain_coreWagonEmbedding
      A hA C.toRelStructure S R f T U preserve hShared μ
  have coreParent (r : CoreEdge) :
      κ ((Witness).parent r) = (Out).parent (CoreActual r) := rfl
  let p : Quotient (U.wagonSetoid μ) := (Witness).parent a
  let q : Quotient (U.wagonSetoid μ) := (Witness).parent c
  have hp : κ p = W₁ := (coreParent a).trans ha
  have hq : κ q = W₂ := (coreParent c).trans hc
  have hxaCore : x ∈ CoreCar a :=
    Eq.mp (congrArg (fun Z : Set Vertex => x ∈ Z)
      (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f a)) hxa
  have hxcCore : x ∈ CoreCar c :=
    Eq.mp (congrArg (fun Z : Set Vertex => x ∈ Z)
      (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f c)) hxc
  have hxCore : x ∈ copyCarrier CoreEmb := by
    obtain ⟨z, _hz, hzx⟩ := hxaCore
    exact ⟨z, hzx⟩
  have hxy : x ≠ y := by
    intro h
    exact hy (Eq.mp (congrArg (fun z : Vertex => z ∈ copyCarrier CoreEmb) h) hxCore)
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
  have hBA : (Train).rel μ (StdEdge i b₀) (CoreActual a) :=
    Quotient.exact (s := (Train).wagonSetoid μ) (hb₀.trans ha.symm)
  have hDC : (Train).rel μ (StdEdge i d₀) (CoreActual c) :=
    Quotient.exact (s := (Train).wagonSetoid μ) (hd₀.trans hc.symm)
  obtain ⟨s₀, _hsOld, hsCore, _hsLocal⟩ :=
    generatedActualASupportTrain_standard_core_copy_local_incidence
      A hA C.toRelStructure S R f T U hShared hRel μ i b₀ a hBA
  obtain ⟨t₀, _htOld, htCore, _htLocal⟩ :=
    generatedActualASupportTrain_standard_core_copy_local_incidence
      A hA C.toRelStructure S R f T U hShared hRel μ i d₀ c hDC
  have hip : (Witness).Meets (.inl i) p :=
    ⟨Emb i s₀, ⟨s₀, rfl⟩, Quotient.sound (s := U.wagonSetoid μ) hsCore⟩
  have hiq : (Witness).Meets (.inl i) q :=
    ⟨Emb i t₀, ⟨t₀, rfl⟩, Quotient.sound (s := U.wagonSetoid μ) htCore⟩
  by_contra hW
  have hpq : p ≠ q := by
    intro h
    exact hW (hp.symm.trans ((congrArg (fun w => κ w) h).trans hq))
  obtain ⟨hBridgeP, hBridgeQ⟩ := OrderOneData.copy_bridges_of_common_wagon_vertex
    Witness hBound i p q x hpq hip hiq ⟨a, rfl, hxaCore⟩ ⟨c, rfl, hxcCore⟩
  obtain ⟨r, hr, hrp, hxr⟩ := hBridgeP
  obtain ⟨s, hs, hsq, hxs⟩ := hBridgeQ
  change r ∈ Set.range (Emb i) at hr
  change s ∈ Set.range (Emb i) at hs
  obtain ⟨u, hu⟩ := hr
  obtain ⟨v, hv⟩ := hs
  have hup : (Witness).parent (Emb i u) = p :=
    (congrArg (fun r : CoreEdge => (Witness).parent r) hu).trans hrp
  have hvq : (Witness).parent (Emb i v) = q :=
    (congrArg (fun r : CoreEdge => (Witness).parent r) hv).trans hsq
  have hxu : x ∈ CoreCar (Emb i u) :=
    Eq.mpr (congrArg (fun r : CoreEdge => x ∈ CoreCar r) hu) hxr
  have hxv : x ∈ CoreCar (Emb i v) :=
    Eq.mpr (congrArg (fun r : CoreEdge => x ∈ CoreCar r) hv) hxs
  have sharedImage (r : SharedEdge) : StdEdge i r.1 = CoreActual (Emb i r) :=
    congrArg
      (fun edge : ActualAPicturePushoutEdge A C.toRelStructure S R I =>
        actualAPictureEdgeEquiv A hA C.toRelStructure S R f edge)
      (physicalStandardEdge_shared
        (sharedOldACarrierInclusion A C.toRelStructure S) Emb i r)
  have sharedParent (r : SharedEdge) (w : Quotient (U.wagonSetoid μ))
      (hr : (Witness).parent (Emb i r) = w) :
      (Out).parent (StdEdge i r.1) = κ w :=
    (congrArg (fun edge : ActualEdge => (Out).parent edge) (sharedImage r)).trans
      ((coreParent (Emb i r)).symm.trans
        (congrArg (fun z : Quotient (U.wagonSetoid μ) => κ z) hr))
  have sharedCarrier (r : SharedEdge) : (StdEdge i r.1).1 = CoreCar (Emb i r) :=
    (congrArg (fun edge : ActualEdge => edge.1) (sharedImage r)).trans
      (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f (Emb i r))
  have hxuStd : x ∈ (StdEdge i u.1).1 :=
    Eq.mpr (congrArg (fun Z : Set Vertex => x ∈ Z) (sharedCarrier u)) hxu
  have hxvStd : x ∈ (StdEdge i v.1).1 :=
    Eq.mpr (congrArg (fun Z : Set Vertex => x ∈ Z) (sharedCarrier v)) hxv
  exact hW (attachedSelectedPicture_same_standard_blocks_parent_eq
    A hA B D C family selected e R f T U hShared μ hRel hOld
    i u.1 b₀ v.1 d₀ x y W₁ W₂ hxy
    ((sharedParent u p hup).trans hp) hb₀
    ((sharedParent v q hvq).trans hq) hd₀ hxuStd hyb₀ hxvStd hyd₀)

end CoreOffCorePair

end StructuralRamsey.Girth

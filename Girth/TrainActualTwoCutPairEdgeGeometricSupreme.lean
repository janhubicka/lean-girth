import Girth.TrainActualTwoCutSymmetricShortSupreme
import Girth.TrainActiveGluingWitness
import Girth.TrainStandardPictureFourWagonBoundary
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Two-cut pair-edge transfer from genuine gluing-image strongness

A physical core edge through the two distinct vertex cut connectors lies
in both prescribed gluing images by A-strongness. Whole-edge containment
is equivalent to membership in each actual shared-edge family. Thus the
same edge is ShortValid toward either standard, without any full witness
system-girth assumption. Physical source locality chooses the singleton
run, and the checked symmetric-short transfer applies the old bound.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

/-- A pair edge through a two-standard witness cycle's two vertex
connectors is short-valid toward either prescribed standard, using only
strongness of those whole gluing images. No witness cycle bound occurs. -/
theorem sharedWitness_two_vertex_pairEdge_shortValid_of_aStrong
    {L : RelLanguage.{u}} {UA X Y I : Type v}
    (A : RelStructure L UA) (B : RelStructure L X) (S : Set X)
    (R : RelStructure L Y)
    (f : I → RelStructure.Embedding (B.induce S) R)
    {m : ℕ} (U : EdgeTrainLevels (OldACarrierEdge A R) m)
    (μ : Fin (m + 1))
    (hStrong : ∀ i : I, AStrong A R (copyCarrier (f i)))
    {c : ℕ} (hc : c = 2)
    (Z : (sharedWitnessOrderOneData U μ
      (sharedOldACarrierCoreEmbedding A B S R f)
      (Subtype.val : OldACarrierEdge A R → Set Y)).BigCycle c)
    (i j : I)
    (hLabel0 : Z.label ⟨0, by omega⟩ = Sum.inl i)
    (hLabel1 : Z.label ⟨1, by omega⟩ = Sum.inl j)
    (x y : Y)
    (hConnector0 : Z.connector ⟨0, by omega⟩ = Sum.inl x)
    (hConnector1 : Z.connector ⟨1, by omega⟩ = Sum.inl y)
    (b : OldACarrierEdge A R) (hbx : x ∈ b.1) (hby : y ∈ b.1) :
    ∀ cut : Fin c, Z.ShortValid
      (sharedWitnessOrderOneData U μ
        (sharedOldACarrierCoreEmbedding A B S R f)
        (Subtype.val : OldACarrierEdge A R → Set Y))
      (trainCyclicPred cut) cut b := by
  subst c
  change Z.label (0 : Fin 2) = Sum.inl i at hLabel0
  change Z.label (1 : Fin 2) = Sum.inl j at hLabel1
  change Z.connector (0 : Fin 2) = Sum.inl x at hConnector0
  change Z.connector (1 : Fin 2) = Sum.inl y at hConnector1
  let W := sharedWitnessOrderOneData U μ
    (sharedOldACarrierCoreEmbedding A B S R f)
    (Subtype.val : OldACarrierEdge A R → Set Y)
  have hxy : x ≠ y := by
    intro heq
    have hSame : Z.connector (0 : Fin 2) = Z.connector 1 := by
      rw [hConnector0, hConnector1, heq]
    exact (by decide : (0 : Fin 2) ≠ 1) (Z.connector_injective hSame)
  have hix : x ∈ W.copyCarrier i := by
    have h := Z.left_incident (0 : Fin 2)
    simpa [OrderOneData.Incident, OrderOneData.carrier,
      hLabel0, hConnector0] using h
  have hjx : x ∈ W.copyCarrier j := by
    have h := Z.right_incident (0 : Fin 2)
    simpa [OrderOneData.Incident, OrderOneData.carrier,
      hLabel1, hConnector0, cyclicSucc] using h
  have hiy : y ∈ W.copyCarrier i := by
    have h := Z.right_incident (1 : Fin 2)
    simpa [OrderOneData.Incident, OrderOneData.carrier,
      hLabel0, hConnector1, cyclicSucc] using h
  have hjy : y ∈ W.copyCarrier j := by
    have h := Z.left_incident (1 : Fin 2)
    simpa [OrderOneData.Incident, OrderOneData.carrier,
      hLabel1, hConnector1] using h
  have hOwned (k : I) (hkx : x ∈ W.copyCarrier k)
      (hky : y ∈ W.copyCarrier k) : b ∈ W.copyEdges k := by
    change b ∈ Set.range (sharedOldACarrierCoreEmbedding A B S R f k)
    apply (sharedOldACarrierCoreEmbedding_mem_range_iff A B S R f k b).mpr
    have hxImage : x ∈ copyCarrier (f k) := by
      obtain ⟨a, ha⟩ := hkx
      exact sharedOldACarrierCoreEmbedding_carrier_subset_local_copy
        A B S R f k a ha
    have hyImage : y ∈ copyCarrier (f k) := by
      obtain ⟨a, ha⟩ := hky
      exact sharedOldACarrierCoreEmbedding_carrier_subset_local_copy
        A B S R f k a ha
    exact oldACarrier_subset_of_two_mem_aStrong
      A R (copyCarrier (f k)) (hStrong k) b x y hxy hbx hby hxImage hyImage
  have hiOwned := hOwned i hix hiy
  have hjOwned := hOwned j hjx hjy
  intro cut
  fin_cases cut
  · change b ∈ W.edges (Z.label (1 : Fin 2)) ∧
      W.Incident (Sum.inr b) (Z.connector (1 : Fin 2)) ∧
      W.Incident (Sum.inr b) (Z.connector (0 : Fin 2))
    exact ⟨by simpa [hLabel1, OrderOneData.edges] using hjOwned,
      by simpa [W, sharedWitnessOrderOneData, OrderOneData.Incident, OrderOneData.carrier,
        hConnector1] using hby,
      by simpa [W, sharedWitnessOrderOneData, OrderOneData.Incident, OrderOneData.carrier,
        hConnector0] using hbx⟩
  · change b ∈ W.edges (Z.label (0 : Fin 2)) ∧
      W.Incident (Sum.inr b) (Z.connector (0 : Fin 2)) ∧
      W.Incident (Sum.inr b) (Z.connector (1 : Fin 2))
    exact ⟨by simpa [hLabel0, OrderOneData.edges] using hiOwned,
      by simpa [W, sharedWitnessOrderOneData, OrderOneData.Incident, OrderOneData.carrier,
        hConnector0] using hbx,
      by simpa [W, sharedWitnessOrderOneData, OrderOneData.Incident, OrderOneData.carrier,
        hConnector1] using hby⟩

section ActualTwoCutPairEdgeGeometricSource

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
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "Selected" => {r : DesignatedCopy B D C family // r ∈ selected}
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- In the exactly-two-cut vertex/vertex pair-edge case, genuine
strongness of the prescribed gluing images supplies both short pieces.
No full system-girth bound on the witness is needed. -/
theorem attachedSelectedPicture_two_cut_pairEdge_geometric_supreme
    [Finite UA]
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a c : OldEdge,
      a ≠ c ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        c.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n) (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwoCuts : cyclicOwnerChanges owner = 2)
    (i j : I)
    (hLabel0 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label ⟨0, by omega⟩ = Sum.inl i)
    (hLabel1 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label ⟨1, by omega⟩ = Sum.inl j)
    (x y : Y)
    (hConnector0 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).connector ⟨0, by omega⟩ = Sum.inl x)
    (hConnector1 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).connector ⟨1, by omega⟩ = Sum.inl y)
    (hPair : (Wit).PairEdge x y)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed (by omega : 2 ≤ cyclicOwnerChanges owner)
  obtain ⟨b, hbx, hby⟩ := hPair
  have hEveryShort : ∀ cut : Fin (cyclicOwnerChanges owner),
      Z.ShortValid Wit (trainCyclicPred cut) cut b :=
    sharedWitness_two_vertex_pairEdge_shortValid_of_aStrong
      A C.toRelStructure S R f U μ hCoreStrong hTwoCuts Z
      i j hLabel0 hLabel1 x y hConnector0 hConnector1 b hbx hby
  have hStandards : ∀ k : Fin (cyclicOwnerChanges owner),
      ∃ s : I, Z.label k = Sum.inl s := by
    intro k
    have hk : k.val = 0 ∨ k.val = 1 := by
      have hkBound := k.isLt
      omega
    rcases hk with hZero | hOne
    · have hk0 : k = (⟨0, by omega⟩ : Fin (cyclicOwnerChanges owner)) :=
        Fin.ext hZero
      rw [hk0]
      exact ⟨i, hLabel0⟩
    · have hk1 : k = (⟨1, by omega⟩ : Fin (cyclicOwnerChanges owner)) :=
        Fin.ext hOne
      rw [hk1]
      exact ⟨j, hLabel1⟩
  exact attachedSelectedPicture_two_cut_symmetric_short_supreme
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwoCopies hOldStrong hCoreStrong
    K hAccept hLinear hn hOrder
    owner hAllowed hTwoCuts hStandards b hEveryShort hOldSupreme

end ActualTwoCutPairEdgeGeometricSource
end StructuralRamsey.Girth

import Girth.TrainActualSupremeCutBoundarySupport
import Girth.TrainActualSharedCoreEdgeStandard

/-!
# Actual order-one cut bridges, without a supreme-label identification

A numerical order-one cut cycle has exactly two connectors, one vertex
and one wagon. The witness bridge bound supplies, for EACH reduced label,
one actual edge incident with BOTH connectors. Transporting that edge to
the attachment gives both original cut incidences simultaneously.

For a standard-labelled reduced occurrence, the chosen edge belongs to a
real shared old support and its physical carrier lies in that whole standard.
This does not identify the reduced gluing label with an original designated
B-label. No acceptability/A1 assumption is made on the reduced cycle; in
particular the edge-only reduced alternative is included.

The remaining order-one transfer must select a source singleton, prove its
boundary-index alignment, retain an original designated occurrence at source
length two, and apply the old bound in the chosen standard. This file does
not claim those conclusions or the full system-girth theorem. No appendix.
-/

namespace StructuralRamsey.Girth
namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- At numerical order one, each label has one physical edge meeting
EVERY connector (there are exactly two). Neither a designated label nor
A1 is assumed, so this includes edge-only reduced words. -/
theorem BigCycle.edge_incident_all_connectors_of_order_one
    (hBound : D.Bound) {n : ℕ} (Z : D.BigCycle n)
    (hOrder : Z.twiceOrder = 2) (k : Fin n) :
    ∃ b : E, b ∈ D.edges (Z.label k) ∧
      ∀ j : Fin n, D.Incident (Sum.inr b) (Z.connector j) := by
  have hn : n = 2 := BigCycle.length_eq_two_of_order_one D Z hOrder
  subst n
  obtain ⟨x, p, hConnectors, hBridge0, hBridge1⟩ :=
    BigCycle.two_both_bridges_of_order_one D hBound Z hOrder
  have hBridge : D.Bridge (Z.label k) x p := by
    fin_cases k
    · exact hBridge0
    · exact hBridge1
  obtain ⟨b, hb, hParent, hx⟩ := hBridge
  have hVertex : D.Incident (Sum.inr b) (Sum.inl x) := hx
  have hWagon : D.Incident (Sum.inr b) (Sum.inr p) := by
    exact ⟨b, rfl, hParent⟩
  refine ⟨b, hb, ?_⟩
  intro j
  rcases hConnectors with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · fin_cases j
    · rw [h0]
      exact hVertex
    · rw [h1]
      exact hWagon
  · fin_cases j
    · rw [h0]
      exact hWagon
    · rw [h1]
      exact hVertex

end OrderOneData

open StructuralRamsey.RelStructure

universe u v
section ActualOrderOneCutBridge

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
local notation "Shared" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
    (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  Emb (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- The order-one witness bound PRODUCES one actual core edge for each
reduced label, incident with both retained ORIGINAL source connectors.
No physical bridge, ShortValid piece, A1, or chosen supreme is postulated. -/
theorem attachedSelectedPicture_orderOne_cut_physical_bridge
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hBound : (Wit).Bound)
    (hOrder : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).twiceOrder = 2)
    (target : Fin (cyclicOwnerChanges owner)) :
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    ∃ b : CoreEdge, b ∈ (Wit).edges (Z.label target) ∧
      ∀ j : Fin (cyclicOwnerChanges owner),
        (Out).Incident (Sum.inr (CoreActual b))
          (K.connector (cyclicOwnerCutIndex owner j)) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨b, hb, hInc⟩ :=
    OrderOneData.BigCycle.edge_incident_all_connectors_of_order_one
      (Wit) hBound Z hOrder target
  refine ⟨b, hb, ?_⟩
  intro j
  have hLift := attachedSelectedPicture_core_edge_incident_lift
    A hA B D C family selected e R f T U hShared hRel μ
    b (Z.connector j) (hInc j)
  have hMap : Sum.map CoreEmb CoreWagon (Z.connector j) =
      K.connector (cyclicOwnerCutIndex owner j) := by
    change Sum.map CoreEmb CoreWagon
      (attachedSelectedPicture_cutConnector
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed j) =
        K.connector (cyclicOwnerCutIndex owner j)
    exact attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j
  simpa only [hMap] using hLift

/-- For a standard-labelled reduced occurrence the bridge additionally
has a genuine shared old source and lies in that whole standard. It is
not claimed to belong to an original designated B-copy. -/
theorem attachedSelectedPicture_orderOne_cut_shared_standard_bridge
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hBound : (Wit).Bound)
    (hOrder : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).twiceOrder = 2)
    (target : Fin (cyclicOwnerChanges owner)) (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i) :
    ∃ s : Shared,
      (CoreActual (Emb i s)).1 ⊆ copyCarrier (Std i) ∧
      ∀ j : Fin (cyclicOwnerChanges owner),
        (Out).Incident (Sum.inr (CoreActual (Emb i s)))
          (K.connector (cyclicOwnerCutIndex owner j)) := by
  obtain ⟨b, hb, hInc⟩ :=
    attachedSelectedPicture_orderOne_cut_physical_bridge
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hBound hOrder target
  rw [hTarget] at hb
  change b ∈ Set.range (Emb i) at hb
  obtain ⟨s, hs⟩ := hb
  refine ⟨s, ?_, ?_⟩
  · exact actualSharedCoreEdge_carrier_subset_standard
      A hA C.toRelStructure S R f i s
  · simpa only [hs] using hInc

end ActualOrderOneCutBridge
end StructuralRamsey.Girth

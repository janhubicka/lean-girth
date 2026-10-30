import Girth.TrainActualCoreLeftShortDescent
import Girth.TrainActualCoreSingletonAutomaticDescent

/-!
# Automatic short absorption into the LEFT supreme standard

The canonical two-cut identity, indexed supreme-plan edge-label
shortness, genuine physical incidence and strong standard carrier
containment already used for right descent are independent of the
orientation of the neighboring standard.

At a source core-owned singleton adjacent to the chosen standard
on the LEFT, the same witnesses and the independently checked
left cyclic owner absorption imply a legal, acceptable short
replacement with strictly fewer minimum cuts.

Nothing asserts the chosen standard must be adjacent to such a
singleton in every positive-cut cycle. No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section CoreSingletonAutomaticLeftDescent

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
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- A real core singleton following the chosen designated supreme
standard has an automatic physical short replacement into that LEFT
standard. No physical bridge, cut alignment, piece type, A2/A3
neighbor inequalities or output owner assignment is assumed. -/
theorem attachedSelectedPicture_core_singleton_supreme_left_descent
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (pos : Fin n) (sourceCore : CoreEdge) (i : I)
    (hCore : owner pos = Sum.inr sourceCore)
    (hPrevOwner : owner (trainCyclicPred pos) = Sum.inl i)
    (target : Fin (cyclicOwnerChanges owner))
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i)
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).HasSupremeAt Wit target) :
    ∃ H : (Out).BigCycle n,
      OrderOneData.BigCycle.PhysicalShortReachable Out K H ∧
      H.Acceptable ∧ H.twiceOrder = K.twiceOrder ∧
      ∃ newOwner : Fin n → I ⊕ CoreEdge,
        (∀ j, GeomAllowed (H.label j) (newOwner j)) ∧
        (∀ other : Fin n → I ⊕ CoreEdge,
          (∀ j, GeomAllowed (H.label j) (other j)) →
          cyclicOwnerChanges newOwner ≤ cyclicOwnerChanges other) ∧
        cyclicOwnerChanges newOwner < cyclicOwnerChanges owner := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨cut, hThis, hPrevious⟩ :=
    attachedSelectedPicture_core_singleton_consecutive_cut_indices
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed pos sourceCore hCore
  have hSource : Z.label cut = Sum.inr sourceCore := by
    change owner (cyclicOwnerCutIndex owner cut) = Sum.inr sourceCore
    rw [hThis]
    exact hCore
  obtain ⟨_pieces, bridge, _hPlan, _hGlobal, _hSelected, hShort⟩ :=
    Z.hasSupremeAt_short_of_edge_label
      Wit target cut i sourceCore hTarget hSource hSupreme
  have hPhysical := attachedSelectedPicture_cut_short_piece_incident_lift
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts target cut bridge hShort
    pos hThis hPrevious
  have hNeighbors := K.shortEdge_ne_neighbors
    Out hAccept hn pos (CoreActual bridge)
    hPhysical.1 hPhysical.2
  have hContained := attachedSelectedPicture_cut_short_piece_carrier_in_standard
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts target cut i hTarget bridge hShort
  obtain ⟨newOwner, hNewAllowed, hMinimal, hDrop,
      hAcceptH, hOrderH⟩ :=
    attachedSelectedPicture_core_left_short_minimal_descent
      A hA B D C family selected e R f T U hShared μ
      K hAccept hn owner hAllowed pos sourceCore i
      hCore hPrevOwner (CoreActual bridge) hContained
      hNeighbors.1 hNeighbors.2 hPhysical.2 hPhysical.1
  let H := K.replaceOne Out pos (Sum.inr (CoreActual bridge))
    hNeighbors.1 hNeighbors.2 hPhysical.2 hPhysical.1
  have hReach : OrderOneData.BigCycle.PhysicalShortReachable Out K H := by
    exact .step K pos (CoreActual bridge)
      hNeighbors.1 hNeighbors.2 hPhysical.2 hPhysical.1 (.refl H)
  exact ⟨H, hReach, hAcceptH, hOrderH,
    newOwner, hNewAllowed, hMinimal, hDrop⟩

end CoreSingletonAutomaticLeftDescent
end StructuralRamsey.Girth

import Girth.TrainActualPositiveCutShortDescent
import Girth.TrainActualPositiveCutShortPieceLift

/-!
# Track A: a REAL reduced short piece produces strict actual cut descent

Combine the genuine physical core-edge lift for a ShortValid reduced
witness piece with the actual one-occurrence short-absorption theorem.
No physical replacement edge is assumed: its exact carrier inclusion
and both output connector incidences are proved from the reduced piece.

Remaining explicit premises are the source singleton/cut index
correspondence and the two neighboring label inequalities. Deriving
those from minimum-segment geometry, and handling long/order-one
alternatives, is separate. This does not assert the full cycle transfer.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualCutShortPieceDescent

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

/-- A genuine reduced ShortValid piece, located at the two cuts of an
actual core-owned singleton, is enough to construct the physical
short absorption and a STRICTLY smaller minimum cyclic segmentation.
The short replacement edge itself and both incidences are derived,
not postulated. For n >= 3 the output stays acceptable and its
numerical order is literally unchanged. -/
theorem attachedSelectedPicture_reduced_short_piece_decreases_cuts
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (pos : Fin n) (sourceCore : CoreEdge) (i : I)
    (hCore : owner pos = Sum.inr sourceCore)
    (hNextOwner : owner (cyclicSucc pos) = Sum.inl i)
    (target cut : Fin (cyclicOwnerChanges owner))
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i)
    (bridge : CoreEdge)
    (hShort : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).ShortValid Wit target cut bridge)
    (hThis : cyclicOwnerCutIndex owner cut = pos)
    (hPrevious : cyclicOwnerCutIndex owner
      (trainCyclicPred cut) = trainCyclicPred pos)
    (hPrevLabel :
      K.label (trainCyclicPred pos) ≠ Sum.inr (CoreActual bridge))
    (hNextLabel :
      Sum.inr (CoreActual bridge) ≠ K.label (cyclicSucc pos)) :
    let H := K.replaceOne Out pos (Sum.inr (CoreActual bridge))
      hPrevLabel hNextLabel
      (attachedSelectedPicture_cut_short_piece_incident_lift
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts target cut bridge hShort
        pos hThis hPrevious).2
      (attachedSelectedPicture_cut_short_piece_incident_lift
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts target cut bridge hShort
        pos hThis hPrevious).1
    ∃ newOwner : Fin n → I ⊕ CoreEdge,
      (∀ j, GeomAllowed (H.label j) (newOwner j)) ∧
      (∀ other : Fin n → I ⊕ CoreEdge,
        (∀ j, GeomAllowed (H.label j) (other j)) →
        cyclicOwnerChanges newOwner ≤ cyclicOwnerChanges other) ∧
      cyclicOwnerChanges newOwner < cyclicOwnerChanges owner ∧
      H.Acceptable ∧ H.twiceOrder = K.twiceOrder := by
  have hPhysical := attachedSelectedPicture_cut_short_piece_incident_lift
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts target cut bridge hShort
    pos hThis hPrevious
  have hContained := attachedSelectedPicture_cut_short_piece_carrier_in_standard
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts target cut i hTarget bridge hShort
  exact attachedSelectedPicture_core_right_short_minimal_descent
    A hA B D C family selected e R f T U hShared μ
    K hAccept hn owner hAllowed pos sourceCore i hCore hNextOwner
    (CoreActual bridge) hContained hPrevLabel hNextLabel
    hPhysical.2 hPhysical.1

end ActualCutShortPieceDescent
end StructuralRamsey.Girth

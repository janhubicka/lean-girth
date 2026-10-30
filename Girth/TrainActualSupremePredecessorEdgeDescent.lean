import Girth.TrainActualCoreSingletonAutomaticDescent
import Girth.TrainCyclicRunWrap

/-!
# A supreme reduced witness with an edge-labelled predecessor descends

At a genuine indexed cut, the reduced label is the original owner
at that cut. If the label immediately PRECEDING a designated supreme
standard i is a physical core edge b, the associated core-owned
source position is automatically a singleton immediately before
standard i: the verified maximal-run identity supplies this fact,
including cyclic wrap.

The checked automatic singleton-short theorem then gives a legal
one-step physical absorption with strictly fewer minimum cuts.
No extra source position, adjacent-standard, short-piece, connector,
or neighbour-label assumptions are introduced.

This handles the edge-predecessor case. The designated predecessor,
possible long pieces, the opposite orientation, and order-one cycles
remain separate. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section SupremePredecessorEdgeDescent

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
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- When the predecessor reduced-witness label of a designated
supreme standard is a genuine CORE EDGE, its source occurrence
admits an automatic legal short absorption with fewer minimal cuts.
The source position and its right-standard owner are constructed
from the canonical cut enumeration, including the cyclic wrap. -/
theorem attachedSelectedPicture_supreme_predecessor_core_edge_descent
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target : Fin (cyclicOwnerChanges owner)) (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i)
    (b : CoreEdge)
    (hPredecessor : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label (trainCyclicPred target) = Sum.inr b)
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
  let pos : Fin n :=
    cyclicOwnerCutIndex owner (trainCyclicPred target)
  have hCore : owner pos = Sum.inr b := by
    change owner (cyclicOwnerCutIndex owner (trainCyclicPred target)) =
      Sum.inr b at hPredecessor
    exact hPredecessor
  have hNextOwner : owner (cyclicSucc pos) = Sum.inl i := by
    have hRun := cyclicOwnerRunLabel_eq_next_cut owner (trainCyclicPred target)
    change owner (cyclicSucc
      (cyclicOwnerCutIndex owner (trainCyclicPred target))) =
      owner (cyclicOwnerCutIndex owner
        (cyclicSucc (trainCyclicPred target))) at hRun
    rw [cyclicSucc_trainCyclicPred_of_two_le hCuts target] at hRun
    have hOwnerTarget :
        owner (cyclicOwnerCutIndex owner target) = Sum.inl i := hTarget
    exact hRun.trans hOwnerTarget
  exact attachedSelectedPicture_core_singleton_supreme_right_descent
    A hA B D C family selected e R f T U hShared hRel μ
    K hAccept hn owner hAllowed hCuts pos b i hCore hNextOwner
    target hTarget hSupreme

end SupremePredecessorEdgeDescent
end StructuralRamsey.Girth

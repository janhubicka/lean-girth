import Girth.TrainActualSupremePredecessorEdgeDescent
import Girth.TrainActualSupremeSuccessorEdgeDescent

/-!
# Positive-cut supreme standard: physical neighbor descent or designated pair

Let an actual positive-cut source cycle have at least three occurrences,
and let a globally legal supreme plan of its exact cut-indexed witness
select standard i. If either immediate REDUCED neighboring label is a
physical core-edge owner, the corresponding single-occurrence physical
short replacement is forced by that global plan, lies in standard i,
and strictly reduces the MINIMUM source owner cut count.

The only remaining nearby-label alternative is that BOTH reduced
neighbors of the selected supreme standard are themselves designated
gluing standards. This is an exact split of all possibilities, not
an assumption that an arbitrary reduced supreme copy has a physical
neighbor. Long/non-singleton geometry of the all-designated case and
order-one are separate obligations. No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualPositiveCutNeighborDichotomy

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

/-- For every genuine globally supreme positive-cut witness on an
acceptable source cycle of length >=3, EITHER an actual admissible
short absorption strictly lowers the minimum geometric cut count,
OR both immediate REDUCED neighbors of the selected supreme
standard have designated gluing-copy labels.

The second disjunct is precisely the next mixed/long segment case,
not a proof that the first always occurs. -/
theorem attachedSelectedPicture_positive_cut_edge_neighbor_or_two_designated
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target : Fin (cyclicOwnerChanges owner)) (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i)
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).HasSupremeAt Wit target) :
    (∃ H : (Out).BigCycle n,
      OrderOneData.BigCycle.PhysicalShortReachable Out K H ∧
      H.Acceptable ∧ H.twiceOrder = K.twiceOrder ∧
      ∃ newOwner : Fin n → I ⊕ CoreEdge,
        (∀ j, GeomAllowed (H.label j) (newOwner j)) ∧
        (∀ other : Fin n → I ⊕ CoreEdge,
          (∀ j, GeomAllowed (H.label j) (other j)) →
          cyclicOwnerChanges newOwner ≤ cyclicOwnerChanges other) ∧
        cyclicOwnerChanges newOwner < cyclicOwnerChanges owner) ∨
    (∃ before after : I,
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts).label (trainCyclicPred target) =
          Sum.inl before ∧
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts).label (cyclicSucc target) =
          Sum.inl after) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  cases hb : Z.label (trainCyclicPred target) with
  | inr b =>
      left
      exact attachedSelectedPicture_supreme_predecessor_core_edge_descent
        A hA B D C family selected e R f T U hShared hRel μ
        K hAccept hn owner hAllowed hCuts target i
        hTarget b hb hSupreme
  | inl before =>
      cases ha : Z.label (cyclicSucc target) with
      | inr b =>
          left
          exact attachedSelectedPicture_supreme_successor_core_edge_descent
            A hA B D C family selected e R f T U hShared hRel μ
            K hAccept hn owner hAllowed hCuts target i
            hTarget b ha hSupreme
      | inl after =>
          right
          exact ⟨before, after, hb, ha⟩

end ActualPositiveCutNeighborDichotomy
end StructuralRamsey.Girth

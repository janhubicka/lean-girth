import Girth.TrainActualCoreSingletonLeftAutomaticDescent
import Girth.TrainCyclicRunWrap

/-!
# Successor reduced physical-edge label gives left short descent

If the witness occurrence immediately FOLLOWING the chosen
designated supreme occurrence has physical core-edge label b, its
source position is a core-owned singleton. Its previous source
position belongs to the selected standard i, by exact canonical cut
enumeration (including wrap). The left automatic short theorem
therefore yields strict minimum-cut descent without any auxiliary
physical edge, neighbor inequalities, cut-index hypotheses or
ownership guesses.

The genuinely designated successor/long-piece situation remains
open; this theorem does not assume it away.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section SupremeSuccessorEdgeDescent

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

/-- The REDUCED witness's immediate successor of a designated
supreme occurrence is a physical edge: it forces a strict positive-cut
absorption into that supreme standard, including cyclic wrap. -/
theorem attachedSelectedPicture_supreme_successor_core_edge_descent
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
    (hSuccessor : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label (cyclicSucc target) = Sum.inr b)
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
  let pos : Fin n := cyclicOwnerCutIndex owner (cyclicSucc target)
  have hCore : owner pos = Sum.inr b := by
    change owner (cyclicOwnerCutIndex owner (cyclicSucc target)) =
      Sum.inr b at hSuccessor
    exact hSuccessor
  obtain ⟨_previousCut, currentCut, _hPrevious, hCurrent⟩ :=
    attachedSelectedPicture_core_singleton_two_cut_indices
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed pos b hCore
  have hIndex : currentCut = cyclicSucc target :=
    (cyclicOwnerCutIndex owner).injective (by simpa [pos] using hCurrent)
  obtain ⟨cut, hThis, hPrevCut⟩ :=
    attachedSelectedPicture_core_singleton_consecutive_cut_indices
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed pos b hCore
  have hCutEq : cut = cyclicSucc target :=
    (cyclicOwnerCutIndex owner).injective (by simpa [pos] using hThis)
  have hPrevPos : cyclicOwnerCutIndex owner target =
      trainCyclicPred pos := by
    rw [hCutEq] at hPrevCut
    simpa [trainCyclicPred_cyclicSucc_of_two_le hCuts target] using hPrevCut
  have hPrevOwner : owner (trainCyclicPred pos) = Sum.inl i := by
    rw [← hPrevPos]
    exact hTarget
  exact attachedSelectedPicture_core_singleton_supreme_left_descent
    A hA B D C family selected e R f T U hShared hRel μ
    K hAccept hn owner hAllowed hCuts pos b i
    hCore hPrevOwner target hTarget hSupreme

end SupremeSuccessorEdgeDescent
end StructuralRamsey.Girth

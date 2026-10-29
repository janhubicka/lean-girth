import Girth.TrainCyclicOwnerAbsorption
import Girth.TrainSingleShortReplacement

/-!
# Track A: strict cyclic-owner descent under a real physical short bridge

The abstract one-position cyclic absorption inequality is instantiated
on an actual selected-picture output BigCycle. A core-owned singleton
relabelled by an incident physical edge inside the RIGHT neighbouring
standard has a better geometric owner assignment. At n >= 3 the real
new BigCycle remains acceptable with the same exact twice-order.
The physical bridge's existence remains an explicit geometric premise;
no appendix or artificial edge/carrier equality is used.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualPositiveCutShortDescent

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

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- An actual core-owned singleton moves into its RIGHT neighbouring
standard by a legal physical short replacement. We construct a valid
new geometric owner assignment and prove STRICTLY fewer cyclic cuts. -/
theorem attachedSelectedPicture_core_right_short_decreases_cuts
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (b : CoreEdge) (i : I)
    (hCore : owner k = Sum.inr b)
    (hNextOwner : owner (cyclicSucc k) = Sum.inl i)
    (edge : ActualEdge) (hInStandard : edge.1 ⊆ copyCarrier (Std i))
    (hPrevLabel : K.label (trainCyclicPred k) ≠ Sum.inr edge)
    (hNextLabel : Sum.inr edge ≠ K.label (cyclicSucc k))
    (hRightInc : (Out).Incident (.inr edge) (K.connector k))
    (hLeftInc : (Out).Incident (.inr edge) (K.connector (trainCyclicPred k))) :
    let H := K.replaceOne Out k (Sum.inr edge)
      hPrevLabel hNextLabel hRightInc hLeftInc
    ∃ nextOwner : Fin n → I ⊕ CoreEdge,
      (∀ j, GeomAllowed (H.label j) (nextOwner j)) ∧
      cyclicOwnerChanges nextOwner < cyclicOwnerChanges owner := by
  let H := K.replaceOne Out k (Sum.inr edge)
    hPrevLabel hNextLabel hRightInc hLeftInc
  let changed := cyclicReplaceOwner owner k (Sum.inl i : I ⊕ CoreEdge)
  have hCoreNe : owner k ≠ Sum.inl i := by
    rw [hCore]
    intro h
    cases h
  have hPredNe : owner (trainCyclicPred k) ≠ owner k := by
    obtain ⟨hBefore, _hAfter⟩ :=
      attachedSelectedPicture_geometric_core_owner_isolated
        A hA B D C family selected e R f T U hShared μ
        K owner hAllowed k b hCore
    intro hEq
    apply hBefore
    rw [hEq]
    exact hCore
  have hDrop : cyclicOwnerChanges changed < cyclicOwnerChanges owner :=
    cyclicOwnerChanges_absorb_right K.length_ge_two
      owner k (Sum.inl i : I ⊕ CoreEdge)
      hNextOwner hCoreNe hPredNe
  refine ⟨changed, ?_, hDrop⟩
  intro j
  by_cases hj : j = k
  · subst j
    have hChanged : changed k = Sum.inl i := by
      simp [changed, cyclicReplaceOwner]
    rw [hChanged]
    have hLabel : H.label k = Sum.inr edge := by
      simp [H, OrderOneData.BigCycle.replaceOne,
        OrderOneData.BigCycle.relabelSameConnectors,
        OrderOneData.BigCycle.replaceLabelAt]
    rw [hLabel]
    change edge.1 ⊆ copyCarrier (Std i)
    exact hInStandard
  · have hChanged : changed j = owner j := by
      simp [changed, cyclicReplaceOwner, hj]
    have hLabel : H.label j = K.label j := by
      simp [H, OrderOneData.BigCycle.replaceOne,
        OrderOneData.BigCycle.relabelSameConnectors,
        OrderOneData.BigCycle.replaceLabelAt, hj]
    rw [hChanged, hLabel]
    exact hAllowed j

/-- The minimum achievable geometric cut count after the short move
is STRICTLY below the previous assignment's count; the new minimum
and its admissibility are constructed rather than assumed. At n>=3,
acceptability and numerical order are also preserved. -/
theorem attachedSelectedPicture_core_right_short_minimal_descent
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (b : CoreEdge) (i : I)
    (hCore : owner k = Sum.inr b)
    (hNextOwner : owner (cyclicSucc k) = Sum.inl i)
    (edge : ActualEdge) (hInStandard : edge.1 ⊆ copyCarrier (Std i))
    (hPrevLabel : K.label (trainCyclicPred k) ≠ Sum.inr edge)
    (hNextLabel : Sum.inr edge ≠ K.label (cyclicSucc k))
    (hRightInc : (Out).Incident (.inr edge) (K.connector k))
    (hLeftInc : (Out).Incident (.inr edge) (K.connector (trainCyclicPred k))) :
    let H := K.replaceOne Out k (Sum.inr edge)
      hPrevLabel hNextLabel hRightInc hLeftInc
    ∃ minOwner : Fin n → I ⊕ CoreEdge,
      (∀ j, GeomAllowed (H.label j) (minOwner j)) ∧
      (∀ alt : Fin n → I ⊕ CoreEdge,
        (∀ j, GeomAllowed (H.label j) (alt j)) →
        cyclicOwnerChanges minOwner ≤ cyclicOwnerChanges alt) ∧
      cyclicOwnerChanges minOwner < cyclicOwnerChanges owner ∧
      H.Acceptable ∧ H.twiceOrder = K.twiceOrder := by
  let H := K.replaceOne Out k (Sum.inr edge)
    hPrevLabel hNextLabel hRightInc hLeftInc
  obtain ⟨nextOwner, hNextAllowed, hDrop⟩ :=
    attachedSelectedPicture_core_right_short_decreases_cuts
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed k b i hCore hNextOwner edge hInStandard
      hPrevLabel hNextLabel hRightInc hLeftInc
  obtain ⟨minOwner, hMinAllowed, hMinimal⟩ :=
    attachedSelectedPicture_cycle_exists_minimal_geometric_owners
      A hA B D C family selected e R f T U hShared μ H
  refine ⟨minOwner, hMinAllowed, hMinimal, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (hMinimal nextOwner hNextAllowed) hDrop
  · exact K.replaceOne_acceptable_of_three_le_length
      Out k (Sum.inr edge) hn hPrevLabel hNextLabel
      hRightInc hLeftInc hAccept
  · exact K.replaceOne_twiceOrder
      Out k (Sum.inr edge) hPrevLabel hNextLabel
      hRightInc hLeftInc

end ActualPositiveCutShortDescent
end StructuralRamsey.Girth

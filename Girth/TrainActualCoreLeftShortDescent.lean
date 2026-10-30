import Girth.TrainActualPositiveCutShortDescent

/-!
# Physical left-neighbour absorption for actual core-owned singletons

A core-owned singleton may instead be adjacent to the chosen standard
on its LEFT.  Its actual physical support-edge replacement is performed
without changing any connectors, and assigning the occurrence to its
left neighbour removes a genuine cyclic cut.  The opposite boundary
was already a cut and cannot create a new one.

These statements require an actual short edge with both incidences,
carrier containment and adjacent-label inequalities; the separate
supreme-witness theorem will derive those premises.

No output linearity or appendix theorem is assumed.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualCoreLeftShortDescent

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

/-- A genuine core singleton whose LEFT neighbour is standard i
can absorb a physically incident edge from that standard while
strictly decreasing its actual number of geometric owner changes.
The source-word cyclic wrap is covered by the generic left
absorption lemma; every other occurrence retains its owner. -/
theorem attachedSelectedPicture_core_left_short_decreases_cuts
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (b : CoreEdge) (i : I)
    (hCore : owner k = Sum.inr b)
    (hPrevOwner : owner (trainCyclicPred k) = Sum.inl i)
    (edge : ActualEdge) (hInStandard : edge.1 ⊆ copyCarrier (Std i))
    (hPrevLabel : K.label (trainCyclicPred k) ≠ Sum.inr edge)
    (hNextLabel : Sum.inr edge ≠ K.label (cyclicSucc k))
    (hRightInc : (Out).Incident (.inr edge) (K.connector k))
    (hLeftInc : (Out).Incident (.inr edge)
      (K.connector (trainCyclicPred k))) :
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
  have hNextNe : owner k ≠ owner (cyclicSucc k) := by
    obtain ⟨_hBefore, hAfter⟩ :=
      attachedSelectedPicture_geometric_core_owner_isolated
        A hA B D C family selected e R f T U hShared μ
        K owner hAllowed k b hCore
    rw [hCore]
    intro h
    exact hAfter h.symm
  have hDrop : cyclicOwnerChanges changed < cyclicOwnerChanges owner :=
    cyclicOwnerChanges_absorb_left K.length_ge_two
      owner k (Sum.inl i : I ⊕ CoreEdge)
      hPrevOwner hCoreNe hNextNe
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

/-- Minimum owner cuts strictly decrease under a legal physical
short absorption into the LEFT neighboring standard.
The new cycle is acceptable and retains its exact twice-order
at source length at least three. -/
theorem attachedSelectedPicture_core_left_short_minimal_descent
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (b : CoreEdge) (i : I)
    (hCore : owner k = Sum.inr b)
    (hPrevOwner : owner (trainCyclicPred k) = Sum.inl i)
    (edge : ActualEdge) (hInStandard : edge.1 ⊆ copyCarrier (Std i))
    (hPrevLabel : K.label (trainCyclicPred k) ≠ Sum.inr edge)
    (hNextLabel : Sum.inr edge ≠ K.label (cyclicSucc k))
    (hRightInc : (Out).Incident (.inr edge) (K.connector k))
    (hLeftInc : (Out).Incident (.inr edge)
      (K.connector (trainCyclicPred k))) :
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
    attachedSelectedPicture_core_left_short_decreases_cuts
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed k b i hCore hPrevOwner edge hInStandard
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

end ActualCoreLeftShortDescent
end StructuralRamsey.Girth

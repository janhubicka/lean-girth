import Girth.TrainActualCutIndexedBigCycle

/-!
# An adjacent reduced standard is literally the adjacent source owner

In the geometrically cut-indexed witness, labels are exactly the
original owner values at the canonical cuts. For an isolated source
occurrence, the designated source standard immediately preceding or
following its reduced label is therefore a genuine *neighbouring*
owner, not merely an arbitrary supreme target.

The two directions use the finite cyclic wrap identity, with no
assumption of a chosen original designated B-label. They provide the
neighbour premise needed by owner-cut descent for a fresh long piece.

This is not yet the full long-insertion theorem. Circulation only.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualReducedNeighborOwner

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
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Exact source provenance of every *reduced* label. This is a
geometric owner value; it need not denote an original designated
source-copy label of the output BigCycle. -/
theorem attachedSelectedPicture_reduced_label_eq_source_owner
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (j : Fin (cyclicOwnerChanges owner)) :
    (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label j =
      owner (cyclicOwnerCutIndex owner j) := by
  rfl

/-- When the predecessor reduced label is standard i and the current
original cut sits after a singleton source occurrence, i is its actual
original LEFT neighbour owner. All cut and standard identities remain
literal. -/
theorem attachedSelectedPicture_reduced_predecessor_is_old_left_owner
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (cut : Fin (cyclicOwnerChanges owner)) (pos : Fin n)
    (hPrevious : cyclicOwnerCutIndex owner
      (trainCyclicPred cut) = trainCyclicPred pos)
    (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label (trainCyclicPred cut) =
        Sum.inl i) :
    owner (trainCyclicPred pos) = Sum.inl i := by
  rw [attachedSelectedPicture_reduced_label_eq_source_owner
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts (trainCyclicPred cut),
    hPrevious] at hTarget
  exact hTarget

/-- The right reduced neighbour is the owner at the next source
occurrence. This uses the wrap-aware maximal-run equation, rather
than incorrectly treating the next *cut index* as the next
source occurrence. -/
theorem attachedSelectedPicture_reduced_successor_is_old_right_owner
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (cut : Fin (cyclicOwnerChanges owner)) (pos : Fin n)
    (hThis : cyclicOwnerCutIndex owner cut = pos)
    (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label (cyclicSucc cut) =
        Sum.inl i) :
    owner (cyclicSucc pos) = Sum.inl i := by
  rw [attachedSelectedPicture_reduced_label_eq_source_owner
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts (cyclicSucc cut)] at hTarget
  have hNext := cyclicOwnerRunLabel_eq_next_cut owner cut
  change owner (cyclicSucc (cyclicOwnerCutIndex owner cut)) =
    owner (cyclicOwnerCutIndex owner (cyclicSucc cut)) at hNext
  calc
    owner (cyclicSucc pos) =
        owner (cyclicSucc (cyclicOwnerCutIndex owner cut)) := by
      rw [hThis]
    _ = owner (cyclicOwnerCutIndex owner (cyclicSucc cut)) := hNext
    _ = Sum.inl i := hTarget

end ActualReducedNeighborOwner
end StructuralRamsey.Girth

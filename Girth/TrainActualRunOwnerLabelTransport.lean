import Girth.TrainCyclicRunIndexAllPositions
import Girth.TrainActualReducedNeighborOwner

/-!
# Path A: exact source-to-reduced-run label transport

For every original selected-picture occurrence (including all cyclic
wraparound positions), the label of the canonically assigned reduced
witness run is EXACTLY the source occurrence's geometric owner.

Thus whenever the reduced run label is the chosen standard index i,
the ORIGINAL occurrence carrier is physically contained in that
attached standard, even if its source label was a foreign designated
B-copy and not literally indexed by i.

This is a bridge for one-pass simultaneous replacement. No constructed
global source plan, no target-independence shortcut, no appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualRunOwnerTransport

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
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Every original occurrence lies in the reduced geometric run
whose label equals its ACTUAL geometric owner, not necessarily its
original designated source label. This covers cyclic wraparound. -/
theorem attachedSelectedPicture_run_index_label_eq_original_owner
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (k : Fin n) :
    (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label
      (cyclicOwnerRunIndex owner (by omega) k) =
        owner k := by
  let hPos : 0 < cyclicOwnerChanges owner := by omega
  let j := cyclicOwnerRunIndex owner hPos k
  have hEq :
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts).label j =
          owner (cyclicOwnerCutIndex owner j) :=
    attachedSelectedPicture_reduced_label_eq_source_owner
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts j
  have hOwner :
      owner k = owner (cyclicOwnerCutIndex owner j) :=
    cyclicOwnerRunIndex_owner_eq_cut owner hPos k
  exact hEq.trans hOwner.symm

/-- If the canonical reduced run of an ORIGINAL occurrence carries
standard i, that source occurrence's genuine physical carrier is
contained in the ACTUAL attached standard i.

In particular a designated source label may be foreign to i:
geometric ownership, rather than literal index equality, is used. -/
theorem attachedSelectedPicture_original_carrier_of_run_standard
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (k : Fin n) (i : I)
    (hRun : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label
        (cyclicOwnerRunIndex owner (by omega) k) = Sum.inl i) :
    (Out).carrier (K.label k) ⊆ copyCarrier (Std i) := by
  have hOwner : owner k = Sum.inl i := by
    have hEq :=
      attachedSelectedPicture_run_index_label_eq_original_owner
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts k
    exact hEq.symm.trans hRun
  have h := hAllowed k
  rw [hOwner] at h
  exact h

/-- The same carrier containment follows when the original
occurrence belongs to a reduced run KEPT by the chosen supreme label.
No source designated-label identity is assumed. -/
theorem attachedSelectedPicture_original_carrier_of_kept_target_run
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target : Fin (cyclicOwnerChanges owner))
    (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i)
    (k : Fin n)
    (hKept : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label
        (cyclicOwnerRunIndex owner (by omega) k) =
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts).label target) :
    (Out).carrier (K.label k) ⊆ copyCarrier (Std i) :=
  attachedSelectedPicture_original_carrier_of_run_standard
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts k i (hKept.trans hTarget)

end ActualRunOwnerTransport
end StructuralRamsey.Girth

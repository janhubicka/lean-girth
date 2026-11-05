import Girth.TrainCyclicRunIndexAllPositions
import Girth.TrainActualReducedNeighborOwner
import Girth.TrainSimultaneousSupreme
import Mathlib.Tactic

/-!
# Path A: a fixed reduced plan can keep only original occurrences in its chosen standard

The one-pass replacement cannot assume that a reduced witness
designated label is literally an original source-copy label.
The witness labels are the GEOMETRIC owners at indexed cuts.

For one SPECIFIED PlanValid witness and a specified supreme target i,
if the piece at the run index of an original source occurrence is
`.keep`, then that original occurrence is geometrically owned by
standard i. This uses the checked total wrap-aware run index,
the checked exact cut-label relation and the actual PlanValid
non-target prohibition on keeping. The original physical label may
still be any designated B-copy or an actual physical edge.

This is an input to, not a proof of, the source one-pass global plan.
Circulation only, no appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section FixedPlanKeptOriginalRun

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

/-- A specified reduced PlanValid witness can keep an indexed run
only if its reduced geometric label equals the chosen target label.

This is not restricted to an existentially chosen witness: it holds
for the precise `pieces` later used by one-pass source expansion. -/
theorem attachedSelectedPicture_plan_keep_run_label_eq_target
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target : Fin (cyclicOwnerChanges owner))
    (pieces : Fin (cyclicOwnerChanges owner) →
      TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)))
    (hPlan : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).PlanValid Wit target pieces)
    (j : Fin (cyclicOwnerChanges owner))
    (hKeep : pieces j = .keep) :
    (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label j =
    (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  by_contra hNot
  have hCase := (hPlan j).2 hNot
  simpa only [hKeep] using hCase

/-- The exact kept-source-owner interface for the one-pass
construction. An original occurrence whose REDUCED run piece is
kept has geometric owner `Sum.inl i`, where i is the target
standard. It need not have the same original designated B-label. -/
theorem attachedSelectedPicture_plan_keep_original_owner
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target : Fin (cyclicOwnerChanges owner))
    (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i)
    (pieces : Fin (cyclicOwnerChanges owner) →
      TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)))
    (hPlan : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).PlanValid Wit target pieces)
    (pos : Fin n)
    (hKeep : pieces (cyclicOwnerRunIndex owner (by omega) pos) = .keep) :
    owner pos = Sum.inl i := by
  have hPos : 0 < cyclicOwnerChanges owner := by omega
  let j := cyclicOwnerRunIndex owner hPos pos
  have hReduced :
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts).label j =
          owner (cyclicOwnerCutIndex owner j) :=
    attachedSelectedPicture_reduced_label_eq_source_owner
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts j
  have hChosen : owner (cyclicOwnerCutIndex owner j) = Sum.inl i := by
    calc
      owner (cyclicOwnerCutIndex owner j) =
        (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed hCuts).label j := hReduced.symm
      _ = (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed hCuts).label target :=
        attachedSelectedPicture_plan_keep_run_label_eq_target
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed hCuts target pieces hPlan j hKeep
      _ = Sum.inl i := hTarget
  have hOwner := cyclicOwnerRunIndex_owner_eq_cut owner hPos pos
  exact hOwner.trans hChosen

end FixedPlanKeptOriginalRun
end StructuralRamsey.Girth

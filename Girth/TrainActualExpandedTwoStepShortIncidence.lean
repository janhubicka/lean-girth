import Girth.TrainActualFixedPlanNonSingletonTwoStep
import Girth.TrainActualChosenTwoStepShortComplete
import Girth.TrainCyclicRunIndexReverseWindow
import Girth.TrainCyclicExpandReducedPieces
import Mathlib.Tactic

/-!
# Path A: physical short incidences at both positions of a fixed-plan two-step run

For ONE specified globally legal reduced PlanValid witness, a LONG
piece at nonadjacent original owner cuts uses an existing original
WAGON connector at the unique intermediate, uncut source position.
The verified reverse run-fibre theorem says an occurrence assigned
to this run is exactly the middle position or its cyclic successor.

The literal expansion of this long piece is a physical FIRST short
at the middle position and a physical SECOND short at its successor.
The existing actual LongValid physical incidence lift proves each
of these shorts meets both adjacent ORIGINAL source connectors.

This handles the old-wagon two-short case in the missing global
LocalPieceIncidence theorem. It uses neither an independently
rechosen supreme plan nor a fresh insertion of an old wagon.
Circulation only; no appendix or manuscript marker promotion.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v

section ActualExpandedTwoStepShortIncidence

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
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Every ORIGINAL source occurrence assigned to a fixed reduced
non-singleton long run is exactly one of its two physical short
positions, and the appropriate mapped core edge is incident with
both ORIGINAL source connectors.

The same reduced `pieces` is used in hPlan, hProduces, the actual
old-wagon classification, and the literal expansion. -/
theorem attachedSelectedPicture_expanded_nonadjacent_long_two_short_incidence
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (target j : Fin (cyclicOwnerChanges owner))
    (pieces : Fin (cyclicOwnerChanges owner) →
      TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)))
    (hPlan : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).PlanValid Wit target pieces)
    (hProduces : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).PlanProducesBigCycle Wit pieces)
    (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ))
    (hp : pieces j = .long first w second)
    (hNotForward : cyclicOwnerCutIndex owner j ≠
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred j)))
    (pos : Fin n)
    (hRun : cyclicOwnerRunIndex owner (by omega) pos = j) :
    ∃ t : Fin n,
      K.connector t = Sum.inr (CoreWagon w) ∧
      ((pos = t ∧
        cyclicExpandReducedPieces owner (by omega) pieces
          CoreActual CoreWagon pos = .short (CoreActual first) ∧
        (Out).Incident (.inr (CoreActual first))
          (K.connector (trainCyclicPred pos)) ∧
        (Out).Incident (.inr (CoreActual first))
          (K.connector pos)) ∨
       (pos = cyclicSucc t ∧
        cyclicExpandReducedPieces owner (by omega) pieces
          CoreActual CoreWagon pos = .short (CoreActual second) ∧
        (Out).Incident (.inr (CoreActual second))
          (K.connector (trainCyclicPred pos)) ∧
        (Out).Incident (.inr (CoreActual second))
          (K.connector pos))) := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hDifferent : Z.label j ≠ Z.label target := by
    intro heq
    have hk := (hPlan j).1 heq
    have impossible :
        (TrainSupremePiece.long first w second :
          TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ))) =
          TrainSupremePiece.keep := hp.symm.trans hk
    cases impossible
  have hLong : Z.LongValid Wit target j first w second := by
    have hc := (hPlan j).2 hDifferent
    simpa only [hp] using hc
  obtain ⟨t, hOld, hUncut, hPrev, hHere⟩ :=
    attachedSelectedPicture_fixed_plan_long_nonadjacent_two_step
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hThree
      target j pieces hPlan hProduces first second w hp hNotForward
  have hUncutOwner : owner t = owner (cyclicSucc t) := by
    by_contra hNe
    exact hUncut ((mem_cyclicOwnerCutPositions_iff owner t).mpr hNe)
  have hExpandPair :=
    cyclicExpandReducedPieces_long_two_step owner hn
      (by omega : 0 < cyclicOwnerChanges owner)
      pieces CoreActual CoreWagon j t
      hUncutOwner hPrev hHere first second w hp
  obtain ⟨hFirstInc, hSecondInc⟩ :=
    attachedSelectedPicture_long_piece_old_wagon_two_short_incidence
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target j
      first second w hLong t hOld hPrev hHere
  have hPosCase : pos = t ∨ pos = cyclicSucc t :=
    cyclicOwnerRunIndex_two_step_fibre owner hn hThree
      j t pos hPrev hHere hRun
  refine ⟨t, hOld, ?_⟩
  rcases hPosCase with hPosT | hPosSucc
  · left
    refine ⟨hPosT, ?_, ?_, ?_⟩
    · rw [hPosT]
      exact hExpandPair.1
    · rw [hPosT]
      exact hFirstInc.1
    · rw [hPosT]
      exact hFirstInc.2
  · right
    refine ⟨hPosSucc, ?_, ?_, ?_⟩
    · rw [hPosSucc]
      exact hExpandPair.2
    · rw [hPosSucc, trainCyclicPred_cyclicSucc_of_two_le
        (by omega : 2 ≤ n) t]
      exact hSecondInc.1
    · rw [hPosSucc]
      exact hSecondInc.2

end ActualExpandedTwoStepShortIncidence
end StructuralRamsey.Girth

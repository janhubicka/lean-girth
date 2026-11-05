import Girth.TrainExpandedRunPhysicalIncidence
import Girth.TrainActualFixedPlanNonSingletonTwoStep
import Girth.TrainActualPositiveCutShortPieceLift
import Girth.TrainActualPositiveCutLongPhysicalLift
import Girth.TrainActualChosenTwoStepShortComplete
import Mathlib.Tactic

/-!
# Path A: physical incidence of the actual one-pass source-expanded plan

For ONE specific globally legal reduced PlanValid/PlanProducesBigCycle
witness with at least three original owner cuts, EVERY source occurrence
in the literal run-indexed expanded plan has the genuine physical
incidence required by the arbitrary legal-replacement theorem.

We use three source cases:
* a reduced short forces a singleton original run; its actual physical
  short is incident with both original connectors;
* a reduced long on a singleton run has the actual PhysicalLongGeometry
  provided by the checked A-strong physical core lift;
* a reduced long on a non-singleton run has exactly two source steps
  around an existing uncut wagon (same fixed plan); both physical
  short incidences are checked in the old-wagon lift.

The generic run-fibre incidence theorem then covers ALL original
source positions, including wrap. No source designated B-copy is
identified with a reduced geometric standard. This is the hInc input
of the already checked global standard-transfer theorem.

Long A2 geometry, global fresh wagons and target standard support are
separate modules. No appendix or manuscript changes.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
section ActualExpandedPlanLocalIncidence

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

/-- An actual fixed globally legal reduced supreme plan determines
a fully LOCAL-INCIDENT source-indexed expanded replacement. This
conclusion is independent of the source's literal designated B-labels,
and uses no extra hypothetical source-replacement legality assumption.

The accepted source cycle has n ≥ 3; the reduced owner word has at
least three genuine cuts. Strongness is the same explicit input needed
by the checked ambient physical nonedge lift for singleton longs. -/
theorem attachedSelectedPicture_fixed_expanded_plan_localIncidence
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (hActive : AStrong A C.toRelStructure S)
    (target : Fin (cyclicOwnerChanges owner))
    (pieces : Fin (cyclicOwnerChanges owner) →
      TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)))
    (hPlan : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).PlanValid Wit target pieces)
    (hProduces : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).PlanProducesBigCycle Wit pieces) :
    K.LocalPieceIncidence Out
      (cyclicExpandReducedPieces owner (by omega) pieces
        CoreActual CoreWagon) := by
  classical
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hShortGeometry :
      ∀ (j : Fin (cyclicOwnerChanges owner)) (b : CoreEdge),
        pieces j = .short b →
          ∃ pos : Fin n,
            cyclicOwnerCutIndex owner j = pos ∧
            cyclicOwnerCutIndex owner (trainCyclicPred j) =
              trainCyclicPred pos ∧
            (Out).Incident (.inr (CoreActual b))
              (K.connector (trainCyclicPred pos)) ∧
            (Out).Incident (.inr (CoreActual b))
              (K.connector pos) := by
    intro j b hp
    have hDiff : Z.label j ≠ Z.label target := by
      intro heq
      have hk := (hPlan j).1 heq
      have hf :
          (TrainSupremePiece.short b :
            TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ))) =
              TrainSupremePiece.keep := hp.symm.trans hk
      cases hf
    have hShort : Z.ShortValid Wit target j b := by
      have hCase := (hPlan j).2 hDiff
      simpa only [hp] using hCase
    have hForward :
        cyclicOwnerCutIndex owner j =
          cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred j)) :=
      attachedSelectedPicture_reduced_short_forces_singleton_three_cuts
        A hA B D C family selected e R f T U hShared hRel μ
        K hAccept owner hAllowed hThree target j b hShort
    let pos : Fin n := cyclicOwnerCutIndex owner j
    have hPrevious :
        cyclicOwnerCutIndex owner (trainCyclicPred j) =
          trainCyclicPred pos := by
      dsimp [pos]
      rw [hForward]
      exact (trainCyclicPred_cyclicSucc_of_two_le
        (by omega : 2 ≤ n)
        (cyclicOwnerCutIndex owner (trainCyclicPred j))).symm
    obtain ⟨hLeft, hRight⟩ :=
      attachedSelectedPicture_cut_short_piece_incident_lift
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts target j b hShort pos rfl hPrevious
    exact ⟨pos, rfl, hPrevious, hLeft, hRight⟩
  have hLongGeometry :
      ∀ (j : Fin (cyclicOwnerChanges owner))
        (first : CoreEdge) (w : Quotient (U.wagonSetoid μ))
        (second : CoreEdge),
        pieces j = .long first w second →
        (∃ pos : Fin n,
          cyclicOwnerCutIndex owner j = pos ∧
          cyclicOwnerCutIndex owner (trainCyclicPred j) =
            trainCyclicPred pos ∧
          K.PhysicalLongGeometry Out pos
            (CoreActual first) (CoreWagon w) (CoreActual second)) ∨
        (∃ t : Fin n,
          cyclicOwnerCutIndex owner j = cyclicSucc t ∧
          cyclicOwnerCutIndex owner (trainCyclicPred j) =
            trainCyclicPred t ∧
          owner t = owner (cyclicSucc t) ∧
          ((Out).Incident (.inr (CoreActual first))
              (K.connector (trainCyclicPred t)) ∧
            (Out).Incident (.inr (CoreActual first))
              (K.connector t)) ∧
          ((Out).Incident (.inr (CoreActual second))
              (K.connector t) ∧
            (Out).Incident (.inr (CoreActual second))
              (K.connector (cyclicSucc t)))) := by
    intro j first w second hp
    have hDiff : Z.label j ≠ Z.label target := by
      intro heq
      have hk := (hPlan j).1 heq
      have hf :
          (TrainSupremePiece.long first w second :
            TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ))) =
              TrainSupremePiece.keep := hp.symm.trans hk
      cases hf
    have hLong : Z.LongValid Wit target j first w second := by
      have hCase := (hPlan j).2 hDiff
      simpa only [hp] using hCase
    by_cases hForward :
        cyclicOwnerCutIndex owner j =
          cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred j))
    · left
      let pos : Fin n := cyclicOwnerCutIndex owner j
      have hPrevious :
          cyclicOwnerCutIndex owner (trainCyclicPred j) =
            trainCyclicPred pos := by
        dsimp [pos]
        rw [hForward]
        exact (trainCyclicPred_cyclicSucc_of_two_le
          (by omega : 2 ≤ n)
          (cyclicOwnerCutIndex owner (trainCyclicPred j))).symm
      have hPhysical : K.PhysicalLongGeometry Out pos
          (CoreActual first) (CoreWagon w) (CoreActual second) :=
        attachedSelectedPicture_reduced_long_piece_physical_output
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed hCuts hActive target j first second w
          hLong pos rfl hPrevious
      exact ⟨pos, rfl, hPrevious, hPhysical⟩
    · right
      obtain ⟨t, hOld, hUncut, hPrev, hHere⟩ :=
        attachedSelectedPicture_fixed_plan_long_nonadjacent_two_step
          A hA B D C family selected e R f T U hShared hRel μ
          K hAccept owner hAllowed hThree target j pieces
          hPlan hProduces first second w hp hForward
      have hUncutOwner : owner t = owner (cyclicSucc t) := by
        by_contra hNe
        exact hUncut
          ((mem_cyclicOwnerCutPositions_iff owner t).mpr hNe)
      obtain ⟨hFirst, hSecond⟩ :=
        attachedSelectedPicture_long_piece_old_wagon_two_short_incidence
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed hCuts target j first second w hLong
          t hOld hPrev hHere
      exact ⟨t, hHere, hPrev, hUncutOwner, hFirst, hSecond⟩
  exact K.expanded_run_plan_localIncidence
    Out hn owner hThree pieces CoreActual CoreWagon
    hShortGeometry hLongGeometry

end ActualExpandedPlanLocalIncidence
end StructuralRamsey.Girth

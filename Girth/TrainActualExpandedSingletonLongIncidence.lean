import Girth.TrainCyclicExpandReducedPieces
import Girth.TrainCyclicRunIndexReverseWindow
import Girth.TrainActualPositiveCutLongPhysicalLift
import Mathlib.Tactic

/-!
# Path A: a fixed reduced singleton LONG lifts to an actual source long

For an ACTUAL fixed reduced PlanValid witness, the physically adjacent
cut endpoints of a singleton reduced long piece identify its unique
ORIGINAL source occurrence. The checked reduced LongValid physical
lift gives the mapped two edges, common wagon, distinctness, both
original boundary incidences and ambient no-pair-edge.

The literal source-plan expansion produces that same physical LONG at
the identified original source position. This discharges the singleton
long branch of the missing original LocalPieceIncidence proof.

Full global source incidence, simultaneous legality, fresh-wagon
transfer and the final supreme conclusion remain separate. This is
circulation-only, without appendix or green manuscript markers.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v

section ActualExpandedSingletonLongIncidence
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

/-- The literal original-cycle plan uses the genuine mapped
physical LONG at the sole source occurrence of a singleton owner
run; its two mapped edges have all required local physical incidence.

The source LongValid ambient non-pair constraint is preserved by
the stated AStrong gluing assumption, not silently omitted. -/
theorem attachedSelectedPicture_expanded_singleton_long_incidence
    {n : ℕ} (K : (Out).BigCycle n)
    (hn : 3 ≤ n)
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
    (j : Fin (cyclicOwnerChanges owner))
    (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ))
    (hp : pieces j = .long first w second)
    (hForward : cyclicOwnerCutIndex owner j =
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred j)))
    (pos : Fin n)
    (hRun : cyclicOwnerRunIndex owner (by omega) pos = j) :
    cyclicOwnerCutIndex owner j = pos ∧
    cyclicExpandReducedPieces owner (by omega) pieces CoreActual
      CoreWagon pos = .long
        (CoreActual first) (CoreWagon w) (CoreActual second) ∧
    (CoreActual first ≠ CoreActual second) ∧
    (Out).Incident (.inr (CoreActual first))
      (K.connector (trainCyclicPred pos)) ∧
    (Out).parent (CoreActual first) = CoreWagon w ∧
    (Out).parent (CoreActual second) = CoreWagon w ∧
    (Out).Incident (.inr (CoreActual second))
      (K.connector pos) := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hDiff : Z.label j ≠ Z.label target := by
    intro heq
    have hk := (hPlan j).1 heq
    have impossible :
        (TrainSupremePiece.long first w second :
          TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ))) =
          TrainSupremePiece.keep := hp.symm.trans hk
    cases impossible
  have hLong : Z.LongValid Wit target j first w second := by
    have hc := (hPlan j).2 hDiff
    simpa only [hp] using hc
  let cutPos : Fin n := cyclicOwnerCutIndex owner j
  have hPrevious : cyclicOwnerCutIndex owner (trainCyclicPred j) =
      trainCyclicPred cutPos := by
    dsimp [cutPos]
    rw [hForward]
    exact (trainCyclicPred_cyclicSucc_of_two_le
      (by omega : 2 ≤ n)
      (cyclicOwnerCutIndex owner (trainCyclicPred j))).symm
  have hAt : pos = cutPos :=
    cyclicOwnerRunIndex_singleton_fibre owner
      (by omega : 2 ≤ n) hCuts j cutPos pos
      hPrevious rfl hRun
  have hHere : cyclicOwnerCutIndex owner j = pos := hAt.symm
  have hPreviousPos : cyclicOwnerCutIndex owner
      (trainCyclicPred j) = trainCyclicPred pos := by
    rw [hAt]
    exact hPrevious
  have hExpanded :
      cyclicExpandReducedPieces owner (by omega) pieces
        CoreActual CoreWagon pos = .long
          (CoreActual first) (CoreWagon w) (CoreActual second) :=
    cyclicExpandReducedPieces_long_singleton owner (by omega)
      pieces CoreActual CoreWagon j pos hHere hPreviousPos
      first second w hp
  have hPhysical : K.PhysicalLongGeometry Out pos
      (CoreActual first) (CoreWagon w) (CoreActual second) :=
    attachedSelectedPicture_reduced_long_piece_physical_output
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hActive
      target j first second w hLong pos hHere hPreviousPos
  obtain ⟨x, y, hAtLeft, hAtRight, hDifferent, hParentFirst,
    hParentSecond, hx, hy, _hNoPair⟩ := hPhysical
  have hIncLeft : (Out).Incident (.inr (CoreActual first))
      (K.connector (trainCyclicPred pos)) := by
    rw [hAtLeft]
    exact hx
  have hIncRight : (Out).Incident (.inr (CoreActual second))
      (K.connector pos) := by
    rw [hAtRight]
    exact hy
  exact ⟨hHere, hExpanded, hDifferent, hIncLeft,
    hParentFirst, hParentSecond, hIncRight⟩

end ActualExpandedSingletonLongIncidence
end StructuralRamsey.Girth

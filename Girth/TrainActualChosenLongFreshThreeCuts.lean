import Girth.TrainPhysicalLongOldWagonA2
import Girth.TrainActualReducedCutFreshness
import Girth.TrainActualPositiveCutLongPhysicalLift
import Mathlib.Tactic

/-!
# Path A: every chosen long piece at an isolated source position is fresh with 3+ cuts

A globally legal supreme witness plan certifies freshness at all original
connectors retained by the cut reduct, but seemingly says nothing about
unretained interior source connectors.

For a long piece whose witness endpoints are exactly the ORIGINAL
consecutive connectors around one source occurrence, this is enough.
Suppose the chosen wagon were an old source connector. The actual
physical-long lift and source A2 force the original cycle length to be 3.
At least three geometric owner changes then force EVERY original
connector to be a retained cut. The existing chosen-plan cut freshness
is contradicted. Thus the wagon is genuinely fresh in the whole source.

This is stronger than the prior all-cut-only theorem, but conditional
on (1) an actually chosen long piece, (2) the exact cut alignment,
(3) strong gluing, and (4) at least 3 owner cuts. Two-cut cycles and
other piece kinds remain separate. No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ChosenLongFreshOfThreeCuts

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
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Above two geometric owner changes, an actual supreme-plan long
piece whose cut connectors surround one original source occurrence
uses a wagon absent from ALL original connectors, not merely the
cut subset. In particular no old-wagon exception survives. -/
theorem attachedSelectedPicture_chosen_long_fresh_of_three_cuts
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThreeCuts : 3 ≤ cyclicOwnerChanges owner)
    (hActive : AStrong A C.toRelStructure S)
    (target cut : Fin (cyclicOwnerChanges owner))
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).HasSupremeAt Wit target)
    (pos : Fin n)
    (hThis : cyclicOwnerCutIndex owner cut = pos)
    (hPrevious : cyclicOwnerCutIndex owner
      (trainCyclicPred cut) = trainCyclicPred pos) :
    let hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    ∃ pieces : Fin (cyclicOwnerChanges owner) →
        TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)),
      Z.PlanValid Wit target pieces ∧
      Z.PlanProducesBigCycle Wit pieces ∧
      (∀ (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ)),
        pieces cut = .long first w second →
        ∀ t : Fin n, K.connector t ≠ Sum.inr (CoreWagon w)) := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨pieces, hPlan, hProduces, hFreshAtCuts⟩ :=
    attachedSelectedPicture_supreme_long_wagon_fresh_at_source_cuts
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target hSupreme
  refine ⟨pieces, hPlan, hProduces, ?_⟩
  intro first second w hp t hOld
  have hDifferent : Z.label cut ≠ Z.label target := by
    intro heq
    have hKeep := (hPlan cut).1 heq
    have hImpossible :
        (TrainSupremePiece.long first w second :
          TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ))) =
          TrainSupremePiece.keep := hp.symm.trans hKeep
    cases hImpossible
  have hLong : Z.LongValid Wit target cut first w second := by
    have hCase := (hPlan cut).2 hDifferent
    simpa only [hp] using hCase
  have hPhysical : K.PhysicalLongGeometry Out pos
      (CoreActual first) (CoreWagon w) (CoreActual second) :=
    attachedSelectedPicture_reduced_long_piece_physical_output
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hActive
      target cut first second w hLong pos hThis hPrevious
  have hEveryCut : ∀ j : Fin n,
      owner j ≠ owner (cyclicSucc j) :=
    K.physicalLong_oldWagon_all_source_cuts Out hn hAccept.2.1
      owner hThreeCuts pos t (CoreActual first)
      (CoreWagon w) (CoreActual second) hPhysical hOld
  have htCut : t ∈ cyclicOwnerCutPositions owner :=
    (mem_cyclicOwnerCutPositions_iff owner t).mpr (hEveryCut t)
  obtain ⟨j, hj⟩ := (cyclicOwnerCutIndex_mem_iff owner t).mp htCut
  exact (hFreshAtCuts cut first second w hp j)
    (by simpa only [hj] using hOld)

end ChosenLongFreshOfThreeCuts
end StructuralRamsey.Girth

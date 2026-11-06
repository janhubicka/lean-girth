import Girth.TrainCyclicExpandReducedPieces
import Girth.TrainCyclicRunIndexReverseWindow
import Girth.TrainActualReducedShortSingleton
import Mathlib.Tactic

/-!
# Path A: a chosen reduced SHORT gives a genuine original singleton short

For a fixed actual reduced PlanValid witness, a SHORT piece can only
lie at a singleton original owner run (source A2/A3). The verified
reverse singleton fibre lemma then identifies EVERY original
occurrence assigned to that run with its actual source cut endpoint.

The literal source-plan expansion is a physical short at precisely
that source position, and the checked core-edge incidence lift
supplies incidences with BOTH original source connectors. No
unverified original designated B-copy membership is assumed.

This is one of the three local-incidence branches of the full one-pass
source replacement; the long/same-wagon branches remain separate.
Circulation only; no appendix or green manuscript markers.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v

section SourceExpandedReducedShortIncidence
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

/-- In an actual specified reduced supreme plan with at least three
owner cuts, every ORIGINAL occurrence assigned to a reduced SHORT
piece is its singleton source cut. The expanded source plan puts
the genuine physical short at that exact source index; it is incident
with both original source connectors.

This works at the last-to-first cyclic wrap as well. -/
theorem attachedSelectedPicture_expanded_reduced_short_incidence
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (target : Fin (cyclicOwnerChanges owner))
    (pieces : Fin (cyclicOwnerChanges owner) →
      TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)))
    (hPlan : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).PlanValid Wit target pieces)
    (j : Fin (cyclicOwnerChanges owner)) (b : CoreEdge)
    (hp : pieces j = .short b)
    (pos : Fin n)
    (hRun : cyclicOwnerRunIndex owner (by omega) pos = j) :
    cyclicOwnerCutIndex owner j = pos ∧
    cyclicExpandReducedPieces owner (by omega) pieces
      CoreActual CoreWagon pos = .short (CoreActual b) ∧
    (Out).Incident (.inr (CoreActual b))
      (K.connector (trainCyclicPred pos)) ∧
    (Out).Incident (.inr (CoreActual b)) (K.connector pos) := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hDiff : Z.label j ≠ Z.label target := by
    intro heq
    have hk := (hPlan j).1 heq
    have impossible :
        (TrainSupremePiece.short b :
          TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ))) =
          TrainSupremePiece.keep := hp.symm.trans hk
    cases impossible
  have hShort : Z.ShortValid Wit target j b := by
    have hc := (hPlan j).2 hDiff
    simpa only [hp] using hc
  have hForward :
      cyclicOwnerCutIndex owner j =
        cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred j)) :=
    attachedSelectedPicture_reduced_short_forces_singleton_three_cuts
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hThree target j b hShort
  let p : Fin n := cyclicOwnerCutIndex owner j
  have hPrevious :
      cyclicOwnerCutIndex owner (trainCyclicPred j) =
        trainCyclicPred p := by
    dsimp [p]
    rw [hForward]
    exact (trainCyclicPred_cyclicSucc_of_two_le
      (by omega : 2 ≤ n)
      (cyclicOwnerCutIndex owner (trainCyclicPred j))).symm
  have hAt : pos = p :=
    cyclicOwnerRunIndex_singleton_fibre owner
      (by omega : 2 ≤ n) hCuts j p pos
      hPrevious rfl hRun
  have hExpanded :
      cyclicExpandReducedPieces owner (by omega) pieces
        CoreActual CoreWagon pos = .short (CoreActual b) :=
    cyclicExpandReducedPieces_short owner (by omega)
      pieces CoreActual CoreWagon j pos hRun b hp
  obtain ⟨hIncLeft, hIncRight⟩ :=
    attachedSelectedPicture_short_original_cut_contacts
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target j b hShort
  have hActualLeft : (Out).Incident (.inr (CoreActual b))
      (K.connector (trainCyclicPred pos)) := by
    rw [hPrevious] at hIncLeft
    exact hAt ▸ hIncLeft
  have hActualRight : (Out).Incident (.inr (CoreActual b))
      (K.connector pos) := by
    exact hAt ▸ hIncRight
  exact ⟨hAt.symm, hExpanded, hActualLeft, hActualRight⟩

end SourceExpandedReducedShortIncidence
end StructuralRamsey.Girth

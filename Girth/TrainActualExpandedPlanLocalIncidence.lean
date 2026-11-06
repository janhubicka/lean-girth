import Girth.TrainActualExpandedReducedShortIncidence
import Girth.TrainActualExpandedTwoStepShortIncidence
import Girth.TrainActualExpandedSingletonLongIncidence
import Mathlib.Tactic

/-!
# Path A: complete original LocalPieceIncidence of one fixed reduced supreme plan

Let an actual selected-picture source cycle have length >=3 and at
least three canonical geometric owner cuts. Take ONE actual reduced
PlanValid and PlanProducesBigCycle witness and expand its SAME plan
to every original source occurrence.

Case split on the reduced piece of the canonical run of an original
occurrence:
* keep: the source expansion keeps it (no local conditions);
* reduced short: source A2/A3 forces singleton original run; the
  verified physical edge lift supplies both source incidences;
* reduced long at singleton: the actual AStrong LongValid physical
  lift supplies distinct edges, both boundary incidences and wagon
  parent equalities;
* reduced long at non-singleton: fixed-plan A2/A3 gives an old wagon
  and an exact two-step original run, with two physical shorts each
  incident with both original connectors.

This theorem closes the local-incidence obligation for the one-pass
positive-cut standard transfer under explicit original strongness,
acceptability and at least three owner cuts. Its separate long A2
geometry, freshness and standard containment are addressed in
independent drafts. No appendix, no manuscript green marker.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v

section ActualExpandedPlanAllIncidence
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

/-- Every original occurrence has a fully physically incident
source-expanded piece when the reduced plan is globally valid and
the original has >=3 geometric cuts. No existential witness is
rechosen; all local cases use the exact same PlanValid pieces. -/
theorem attachedSelectedPicture_expanded_plan_localPieceIncidence
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
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
  have hPos : 0 < cyclicOwnerChanges owner := by omega
  change K.LocalPieceIncidence Out
    (cyclicExpandReducedPieces owner hPos pieces CoreActual CoreWagon)
  intro pos
  let j := cyclicOwnerRunIndex owner hPos pos
  cases hp : pieces j with
  | keep =>
      have hExpanded :
          cyclicExpandReducedPieces owner hPos pieces CoreActual
            CoreWagon pos = .keep :=
        cyclicExpandReducedPieces_keep owner hPos pieces
          CoreActual CoreWagon j pos rfl hp
      simpa [hExpanded]
  | short b =>
      obtain ⟨_hAt, hExpanded, hLeft, hRight⟩ :=
        attachedSelectedPicture_expanded_reduced_short_incidence
          A hA B D C family selected e R f T U hShared hRel μ
          K hAccept hn owner hAllowed hThree
          target pieces hPlan j b hp pos rfl
      simpa [hExpanded] using And.intro hLeft hRight
  | long first w second =>
      by_cases hForward :
          cyclicOwnerCutIndex owner j =
            cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred j))
      · obtain ⟨_hAt, hExpanded, hDistinct, hLeft,
          hParentFirst, hParentSecond, hRight⟩ :=
          attachedSelectedPicture_expanded_singleton_long_incidence
            A hA B D C family selected e R f T U hShared hRel μ
            K hn owner hAllowed hThree hActive
            target pieces hPlan j first second w hp hForward pos rfl
        have hLocal :
            CoreActual first ≠ CoreActual second ∧
            (Out).Incident (.inr (CoreActual first))
              (K.connector (trainCyclicPred pos)) ∧
            (Out).parent (CoreActual first) = CoreWagon w ∧
            (Out).parent (CoreActual second) = CoreWagon w ∧
            (Out).Incident (.inr (CoreActual second))
              (K.connector pos) :=
          ⟨hDistinct, hLeft, hParentFirst, hParentSecond, hRight⟩
        simpa [hExpanded] using hLocal
      · obtain ⟨t, _hOld, hCase⟩ :=
          attachedSelectedPicture_expanded_nonadjacent_long_two_short_incidence
            A hA B D C family selected e R f T U hShared hRel μ
            K hAccept hn owner hAllowed hThree
            target j pieces hPlan hProduces
            first second w hp hForward pos rfl
        rcases hCase with ⟨_hAt, hExpanded, hLeft, hRight⟩ |
          ⟨_hAt, hExpanded, hLeft, hRight⟩
        · simpa [hExpanded] using And.intro hLeft hRight
        · simpa [hExpanded] using And.intro hLeft hRight

end ActualExpandedPlanAllIncidence
end StructuralRamsey.Girth

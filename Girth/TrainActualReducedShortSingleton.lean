import Girth.TrainPhysicalTwoContactsAdjacent
import Girth.TrainActualPositiveCutShortPieceLift
import Girth.TrainActualThreeCutNonadjacentLong
import Girth.TrainActualReducedCutFreshness
import Mathlib.Tactic

/-!
# Path A: an actual reduced ShortValid piece cannot span a non-singleton run

The genuine cut-indexed witness has literal connectors mapping to the
ORIGINAL source connectors at the canonical owner cuts. A ShortValid
reduced witness piece supplies one actual physical core A-edge incident
with both mapped original boundary connectors, without assuming either
source cut is adjacent to the other.

Source A2/A3 forces any two distinct positions incident with one
physical edge to be cyclically adjacent. When there are >=3 owner cuts,
reverse adjacency is excluded by the checked canonical cut order, so
the original run must be a singleton.

An actual globally chosen supreme plan therefore uses a LONG piece at
every non-target, non-singleton reduced position (and hence, by the
checked A2/A3 long theorem, that source run has exactly two steps).
No appendix, no manuscript green marker before exact-head CI.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ReducedShortSingleton

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
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
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

/-- Actual reduced short incidence transports to BOTH original indexed
cut connectors for any run length; no singleton/alignment assumption.
The two endpoints are the literal cutIndex(pred cut), cutIndex(cut). -/
theorem attachedSelectedPicture_short_original_cut_contacts
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (b : CoreEdge)
    (hShort : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).ShortValid Wit target cut b) :
    (Out).Incident (.inr (CoreActual b))
      (K.connector (cyclicOwnerCutIndex owner (trainCyclicPred cut))) ∧
    (Out).Incident (.inr (CoreActual b))
      (K.connector (cyclicOwnerCutIndex owner cut)) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hMap (j : Fin (cyclicOwnerChanges owner)) :
      Sum.map CoreEmb CoreWagon (Z.connector j) =
        K.connector (cyclicOwnerCutIndex owner j) := by
    change Sum.map CoreEmb CoreWagon
      (attachedSelectedPicture_cutConnector
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed j) =
        K.connector (cyclicOwnerCutIndex owner j)
    exact attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j
  have hLeft := attachedSelectedPicture_core_edge_incident_lift
    A hA B D C family selected e R f T U hShared hRel μ
    b (Z.connector (trainCyclicPred cut)) hShort.2.1
  have hRight := attachedSelectedPicture_core_edge_incident_lift
    A hA B D C family selected e R f T U hShared hRel μ
    b (Z.connector cut) hShort.2.2
  rw [hMap (trainCyclicPred cut)] at hLeft
  rw [hMap cut] at hRight
  exact ⟨hLeft, hRight⟩

/-- A genuine reduced ShortValid piece, spanning two distinct original
owner-cut positions, forces those positions to be cyclic neighbours.
The source acceptability A2/A3 is used on ACTUAL physical connectors. -/
theorem attachedSelectedPicture_reduced_short_cuts_adjacent
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (b : CoreEdge)
    (hShort : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).ShortValid Wit target cut b) :
    cyclicOwnerCutIndex owner cut =
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut)) ∨
    cyclicOwnerCutIndex owner (trainCyclicPred cut) =
      cyclicSucc (cyclicOwnerCutIndex owner cut) := by
  have hDifferentCut : trainCyclicPred cut ≠ cut := by
    intro hEq
    have hBack := cyclicSucc_trainCyclicPred_of_two_le hCuts cut
    rw [hEq] at hBack
    exact (cyclicSucc_ne_self_of_two_le hCuts cut) hBack
  have hDistinctOriginal :
      cyclicOwnerCutIndex owner (trainCyclicPred cut) ≠
        cyclicOwnerCutIndex owner cut := by
    intro hEq
    exact hDifferentCut ((cyclicOwnerCutIndex owner).injective hEq)
  obtain ⟨hLeft, hRight⟩ :=
    attachedSelectedPicture_short_original_cut_contacts
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target cut b hShort
  exact K.physical_edge_two_contacts_adjacent
    Out hAccept (CoreActual b)
      (cyclicOwnerCutIndex owner (trainCyclicPred cut))
      (cyclicOwnerCutIndex owner cut)
      hDistinctOriginal hLeft hRight

/-- With three or more original owner cuts, REVERSE adjacency
of consecutive cut indices is impossible. Hence a reduced short
piece can only occur at an ORIGINAL singleton owner segment. -/
theorem attachedSelectedPicture_reduced_short_forces_singleton_three_cuts
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (b : CoreEdge)
    (hShort : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).ShortValid Wit target cut b) :
    cyclicOwnerCutIndex owner cut =
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut)) := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  have hAdj :=
    attachedSelectedPicture_reduced_short_cuts_adjacent
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hCuts target cut b hShort
  rcases hAdj with hForward | hReverse
  · exact hForward
  · exact False.elim
      ((cyclicOwnerCutIndex_pred_ne_reverse_succ_of_three_cuts
        owner hThree cut) hReverse)

/-- For ANY SPECIFIED globally legal chosen plan, the piece at a
non-target, non-singleton reduced cut must be long. Unlike an
existential-only statement, this theorem can be applied to the EXACT
same selected-plan witness used by later physical transfer theorems. -/
theorem attachedSelectedPicture_any_plan_nontarget_nonsingleton_is_long
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (pieces : Fin (cyclicOwnerChanges owner) →
      TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)))
    (hPlan : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).PlanValid Wit target pieces)
    (hDifferent : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label cut ≠
      (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label target)
    (hNonSingleton : cyclicOwnerCutIndex owner cut ≠
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut))) :
    let hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    ∃ first second : CoreEdge, ∃ w : Quotient (U.wagonSetoid μ),
      pieces cut = .long first w second ∧
      Z.LongValid Wit target cut first w second := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hCase := (hPlan cut).2 hDifferent
  cases hp : pieces cut with
  | keep =>
      have hf : False := by
        simpa only [hp] using hCase
      exact False.elim hf
  | short b =>
      have hShort : Z.ShortValid Wit target cut b := by
        simpa only [hp] using hCase
      have hForward :=
        attachedSelectedPicture_reduced_short_forces_singleton_three_cuts
          A hA B D C family selected e R f T U hShared hRel μ
          K hAccept owner hAllowed hThree target cut b hShort
      exact False.elim (hNonSingleton hForward)
  | long first w second =>
      have hLong : Z.LongValid Wit target cut first w second := by
        simpa only [hp] using hCase
      exact ⟨first, second, w, rfl, hLong⟩

/-- From a GENUINELY chosen globally legal plan, every NON-TARGET
piece at a NON-singleton original owner segment must be LongValid:
the short alternative violates source A2/A3, and a kept piece is
forbidden by PlanValid. The claim remains conditional on having
that non-target cut and does NOT assert a rank descent. -/
theorem attachedSelectedPicture_chosen_nontarget_nonsingleton_is_long
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).HasSupremeAt Wit target)
    (hDifferent : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label cut ≠
      (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label target)
    (hNonSingleton : cyclicOwnerCutIndex owner cut ≠
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut))) :
    let hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    ∃ pieces : Fin (cyclicOwnerChanges owner) →
        TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)),
      Z.PlanValid Wit target pieces ∧
      Z.PlanProducesBigCycle Wit pieces ∧
      (∃ first second : CoreEdge, ∃ w : Quotient (U.wagonSetoid μ),
        pieces cut = .long first w second ∧
        Z.LongValid Wit target cut first w second) := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨pieces, hPlan, hProduces, _hFresh⟩ :=
    attachedSelectedPicture_supreme_long_wagon_fresh_at_source_cuts
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target hSupreme
  refine ⟨pieces, hPlan, hProduces, ?_⟩
  exact attachedSelectedPicture_any_plan_nontarget_nonsingleton_is_long
    A hA B D C family selected e R f T U hShared hRel μ
    K hAccept owner hAllowed hThree
    target cut pieces hPlan hDifferent hNonSingleton

end ReducedShortSingleton
end StructuralRamsey.Girth

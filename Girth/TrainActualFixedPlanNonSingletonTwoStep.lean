import Girth.TrainActualChosenTwoStepLong
import Girth.TrainActualReducedShortSingleton
import Girth.TrainOptionalFreshnessConverse
import Mathlib.Tactic

/-!
# Path A: a specified reduced supreme plan has exact original two-step long geometry

Prior chosen-long results return an existential selected supreme plan.
Simultaneous original-source expansion requires identifying ONE fixed
`pieces` witness through PlanValid, PlanProducesBigCycle, the source
wagon and the replacement edges. This file removes that hidden
existential plan switching.

A genuine reduced long piece spanning nonadjacent original cut
connectors has an existing wagon by A3; exact freshness at retained
cut connectors places it at an UNCUT original position; source A2
and cyclic three-cut indexing orient the two original boundaries
as predecessor and successor of that wagon position.

Both geometry and short-exclusion now apply to the SAME given plan.
This is a building block for full source LocalPieceIncidence; it
does not construct an original-cycle output. Circulation only.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v

section FixedPlanNonSingletonLongTwoStep

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
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- A genuine reduced LongValid piece spanning nonadjacent original
cut boundaries is forced to use exactly one existing UNCUT original
wagon connector between them. The input freshness is only for the
selected wagon at all ORIGINAL CUT connectors, not the full source.

This geometric lemma does not choose a supreme plan at all. -/
theorem attachedSelectedPicture_long_nonadjacent_two_step_of_cut_fresh
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ))
    (hLong : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).LongValid Wit
        target cut first w second)
    (hCutFresh : ∀ j : Fin (cyclicOwnerChanges owner),
      K.connector (cyclicOwnerCutIndex owner j) ≠
        Sum.inr (CoreWagon w))
    (hNotForward : cyclicOwnerCutIndex owner cut ≠
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut))) :
    ∃ t : Fin n,
      K.connector t = Sum.inr (CoreWagon w) ∧
      t ∉ cyclicOwnerCutPositions owner ∧
      cyclicOwnerCutIndex owner (trainCyclicPred cut) =
        trainCyclicPred t ∧
      cyclicOwnerCutIndex owner cut = cyclicSucc t := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  have hNotReverse :
      cyclicOwnerCutIndex owner (trainCyclicPred cut) ≠
        cyclicSucc (cyclicOwnerCutIndex owner cut) :=
    cyclicOwnerCutIndex_pred_ne_reverse_succ_of_three_cuts
      owner hThree cut
  obtain ⟨t, hOld⟩ :=
    attachedSelectedPicture_long_cut_piece_wagon_is_old_connector
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hCuts target cut
      first second w hLong
      (cyclicOwnerCutIndex owner (trainCyclicPred cut))
      (cyclicOwnerCutIndex owner cut)
      rfl rfl hNotForward hNotReverse
  have hUncut : t ∉ cyclicOwnerCutPositions owner := by
    intro ht
    obtain ⟨j, hj⟩ := (cyclicOwnerCutIndex_mem_iff owner t).mp ht
    exact (hCutFresh j) (by simpa only [hj] using hOld)
  obtain ⟨hContactA, hContactB⟩ :=
    attachedSelectedPicture_long_cut_piece_actual_source_contacts
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target cut first second w hLong
  have hDistinctReduced : trainCyclicPred cut ≠ cut := by
    intro heq
    have hBack := cyclicSucc_trainCyclicPred_of_two_le hCuts cut
    rw [heq] at hBack
    exact (cyclicSucc_ne_self_of_two_le hCuts cut) hBack
  have hDistinctOriginal :
      cyclicOwnerCutIndex owner (trainCyclicPred cut) ≠
        cyclicOwnerCutIndex owner cut := by
    intro heq
    exact hDistinctReduced ((cyclicOwnerCutIndex owner).injective heq)
  have hStraddle :=
    K.old_wagon_distinct_contacts_straddle
      Out hAccept.2.1 (CoreWagon w) t
      (cyclicOwnerCutIndex owner (trainCyclicPred cut))
      (cyclicOwnerCutIndex owner cut)
      hOld hContactA hContactB hDistinctOriginal
  have hOrientation :=
    cyclicOwnerCutIndex_old_uncut_straddle_forward_of_three_cuts
      owner hThree cut t hUncut hStraddle
  exact ⟨t, hOld, hUncut, hOrientation.1, hOrientation.2⟩

/-- The same conclusion for an EXPLICIT fixed reduced plan which
produces an actual globally legal replacement word. No rechoosing
the selected supreme plan is allowed in this statement. -/
theorem attachedSelectedPicture_fixed_plan_long_nonadjacent_two_step
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
    (hProduces : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).PlanProducesBigCycle Wit pieces)
    (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ))
    (hp : pieces cut = .long first w second)
    (hNotForward : cyclicOwnerCutIndex owner cut ≠
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut))) :
    ∃ t : Fin n,
      K.connector t = Sum.inr (CoreWagon w) ∧
      t ∉ cyclicOwnerCutPositions owner ∧
      cyclicOwnerCutIndex owner (trainCyclicPred cut) =
        trainCyclicPred t ∧
      cyclicOwnerCutIndex owner cut = cyclicSucc t := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hDiff : Z.label cut ≠ Z.label target := by
    intro heq
    have hk := (hPlan cut).1 heq
    have hf :
        (TrainSupremePiece.long first w second :
          TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ))) =
          TrainSupremePiece.keep := hp.symm.trans hk
    cases hf
  have hLong : Z.LongValid Wit target cut first w second := by
    have hCase := (hPlan cut).2 hDiff
    simpa only [hp] using hCase
  obtain ⟨outLength, H, hWord⟩ := hProduces
  have hReducedFresh :
      ∀ j : Fin (cyclicOwnerChanges owner),
        Z.connector j ≠ Sum.inr w :=
    Z.longWagons_fresh_of_literalBigCycle
      Wit H pieces hWord cut first w second hp
  have hCutFresh :
      ∀ j : Fin (cyclicOwnerChanges owner),
        K.connector (cyclicOwnerCutIndex owner j) ≠
          Sum.inr (CoreWagon w) :=
    attachedSelectedPicture_reduced_wagon_fresh_at_all_source_cuts
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts w hReducedFresh
  exact attachedSelectedPicture_long_nonadjacent_two_step_of_cut_fresh
    A hA B D C family selected e R f T U hShared hRel μ
    K hAccept owner hAllowed hThree target cut first second w
    hLong hCutFresh hNotForward

/-- At EVERY non-target non-singleton run of one specified globally
legal reduced plan, the actual chosen piece is a long piece and its
original source segment has EXACTLY two positions around an existing
uncut wagon. This uses the SAME pieces throughout, including the
short-exclusion and global reduced-word freshness witnesses. -/
theorem attachedSelectedPicture_fixed_plan_nontarget_nonadjacent_two_step
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
    (hProduces : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).PlanProducesBigCycle Wit pieces)
    (hDiff : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label cut ≠
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed (by omega)).label target)
    (hNotForward : cyclicOwnerCutIndex owner cut ≠
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut))) :
    ∃ first second : CoreEdge, ∃ w : Quotient (U.wagonSetoid μ),
    ∃ t : Fin n,
      pieces cut = .long first w second ∧
      K.connector t = Sum.inr (CoreWagon w) ∧
      t ∉ cyclicOwnerCutPositions owner ∧
      cyclicOwnerCutIndex owner (trainCyclicPred cut) =
        trainCyclicPred t ∧
      cyclicOwnerCutIndex owner cut = cyclicSucc t := by
  obtain ⟨first, second, w, hp, _hLong⟩ :=
    attachedSelectedPicture_any_plan_nontarget_nonsingleton_is_long
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hThree target cut pieces
      hPlan hDiff hNotForward
  obtain ⟨t, hOld, hUncut, hPrev, hHere⟩ :=
    attachedSelectedPicture_fixed_plan_long_nonadjacent_two_step
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hThree target cut pieces hPlan hProduces
      first second w hp hNotForward
  exact ⟨first, second, w, t, hp, hOld, hUncut, hPrev, hHere⟩

end FixedPlanNonSingletonLongTwoStep
end StructuralRamsey.Girth

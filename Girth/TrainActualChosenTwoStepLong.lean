import Girth.TrainActualTwoStepCutOrientation
import Girth.TrainActualPositiveCutLongWagonExisting
import Mathlib.Tactic

/-!
# Path A: a genuine chosen non-singleton long piece spans exactly two source steps

The finite orientation lemma for a one-uncut gap is combined with
ACTUAL LongValid physical contacts and the SAME globally chosen
HasSupremeAt plan. The old wagon guaranteed by A3 must occur at an
uncut original position, and source A2 forces the original cut
connectors to be its predecessor and successor, in that order.

Thus every chosen long piece spanning a non-singleton source run,
when at least three owner cuts exist, has exactly one intermediate
uncut connector and it is the old wagon.

This is an exact physical obstruction, NOT a claim of legal
two-short replacement or a completed positive-cut descent.
Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualChosenTwoStepLong

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

/-- A genuine reduced LongValid physical piece yields actual source
wagon contacts at BOTH original cut connectors. Unlike the A3
existing-wagon theorem, this is also useful when the wagon is fresh.
No old source wagon or cycle acceptability is assumed. -/
theorem attachedSelectedPicture_long_cut_piece_actual_source_contacts
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ))
    (hLong : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).LongValid Wit target cut first w second) :
    K.InWagonAt (CoreWagon w)
        (cyclicOwnerCutIndex owner (trainCyclicPred cut)) ∧
      K.InWagonAt (CoreWagon w)
        (cyclicOwnerCutIndex owner cut) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨x, y, hPrev, hHere, _hFirst, _hSecond, _hDistinct,
    hParentFirst, hParentSecond, hFirstX, hSecondY, _hNoPair⟩ := hLong
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
  have hAtA : K.connector
      (cyclicOwnerCutIndex owner (trainCyclicPred cut)) =
        Sum.inl (CoreEmb x) := by
    have h := hMap (trainCyclicPred cut)
    rw [hPrev] at h
    exact h.symm
  have hAtB : K.connector (cyclicOwnerCutIndex owner cut) =
      Sum.inl (CoreEmb y) := by
    have h := hMap cut
    rw [hHere] at h
    exact h.symm
  have hWagonX : (Out).WagonVertex (CoreWagon w) (CoreEmb x) := by
    refine ⟨CoreActual first, ?_, ?_⟩
    · change CoreWagon ((Wit).parent first) = CoreWagon w
      exact congrArg CoreWagon hParentFirst
    · change (CoreEmb x) ∈ (CoreActual first).1
      rw [actualAPictureEdgeEquiv_core_carrier
        A hA C.toRelStructure S R f first]
      exact ⟨x, hFirstX, rfl⟩
  have hWagonY : (Out).WagonVertex (CoreWagon w) (CoreEmb y) := by
    refine ⟨CoreActual second, ?_, ?_⟩
    · change CoreWagon ((Wit).parent second) = CoreWagon w
      exact congrArg CoreWagon hParentSecond
    · change (CoreEmb y) ∈ (CoreActual second).1
      rw [actualAPictureEdgeEquiv_core_carrier
        A hA C.toRelStructure S R f second]
      exact ⟨y, hSecondY, rfl⟩
  exact ⟨⟨CoreEmb x, hAtA, hWagonX⟩,
    ⟨CoreEmb y, hAtB, hWagonY⟩⟩

/-- At least three source owner cuts: a genuinely selected long piece
with NONADJACENT original cut boundaries reuses an original wagon
connector at precisely the unique intermediate uncut source position.
The two boundary cut indices are its predecessor and successor IN THAT
ORDER (hence the selected non-singleton run has exactly two steps). -/
theorem attachedSelectedPicture_chosen_nonadjacent_long_exact_two_step
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThreeCuts : 3 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).HasSupremeAt Wit target)
    (hNotForward : cyclicOwnerCutIndex owner cut ≠
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut))) :
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
        ∃ t : Fin n, K.connector t = Sum.inr (CoreWagon w) ∧
          t ∉ cyclicOwnerCutPositions owner ∧
          cyclicOwnerCutIndex owner (trainCyclicPred cut) =
            trainCyclicPred t ∧
          cyclicOwnerCutIndex owner cut = cyclicSucc t) := by
  classical
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨pieces, hPlan, hProduces, hOldUncut⟩ :=
    attachedSelectedPicture_chosen_forward_nonadjacent_long_old_uncut_wagon
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hThreeCuts target cut hSupreme
      hNotForward
  refine ⟨pieces, hPlan, hProduces, ?_⟩
  intro first second w hp
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
  obtain ⟨t, hOld, hUncut⟩ := hOldUncut first second w hp
  obtain ⟨hContactA, hContactB⟩ :=
    attachedSelectedPicture_long_cut_piece_actual_source_contacts
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target cut first second w hLong
  have hDistinctCut : trainCyclicPred cut ≠ cut := by
    intro hEq
    have hBack := cyclicSucc_trainCyclicPred_of_two_le
      (by omega : 2 ≤ cyclicOwnerChanges owner) cut
    rw [hEq] at hBack
    exact (cyclicSucc_ne_self_of_two_le
      (by omega : 2 ≤ cyclicOwnerChanges owner) cut) hBack
  have hDistinctOriginal :
      cyclicOwnerCutIndex owner (trainCyclicPred cut) ≠
        cyclicOwnerCutIndex owner cut := by
    intro hEq
    exact hDistinctCut ((cyclicOwnerCutIndex owner).injective hEq)
  have hStraddle :=
    K.old_wagon_distinct_contacts_straddle
      Out hAccept.2.1 (CoreWagon w) t
      (cyclicOwnerCutIndex owner (trainCyclicPred cut))
      (cyclicOwnerCutIndex owner cut)
      hOld hContactA hContactB hDistinctOriginal
  have hOrientation :=
    cyclicOwnerCutIndex_old_uncut_straddle_forward_of_three_cuts
      owner hThreeCuts cut t hUncut hStraddle
  exact ⟨t, hOld, hUncut, hOrientation.1, hOrientation.2⟩

end ActualChosenTwoStepLong
end StructuralRamsey.Girth

import Girth.TrainActualChosenTwoStepLong
import Girth.TrainTwoConsecutiveShortComplete
import Mathlib.Tactic

/-!
# Path A: an old-wagon long piece produces two legal physical short pieces

When a genuinely selected non-singleton reduced LongValid piece reuses
one ORIGINAL uncut connector wagon, the verified exact two-step
classification identifies its source neighbours. The same two
physical core edges are incident with the two ORIGINAL source
occurrences on either side of the old wagon.

Replacing these two occurrences by SHORT physical pieces (keeping the
original wagon connector) avoids the fresh-wagon obstruction entirely.
The arbitrary complete replacement lemma makes the output an actual
acceptable BigCycle, retains exact numerical order and pulls every
supreme label back to the source.

This does not show strict minimum owner/designated lex descent.
That is the remaining positive-cut obligation; no appendix or TeX.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualChosenTwoStepShort

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

/-- In a genuine selected long whose wagon is already the middle
original connector, the SAME two physical LongValid edges satisfy
the full local incidence required by two consecutive SHORT source
replacements. There is no need to insert the old wagon. -/
theorem attachedSelectedPicture_long_piece_old_wagon_two_short_incidence
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ))
    (hLong : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).LongValid Wit target cut first w second)
    (t : Fin n)
    (hOld : K.connector t = Sum.inr (CoreWagon w))
    (hPrevBoundary : cyclicOwnerCutIndex owner (trainCyclicPred cut) =
      trainCyclicPred t)
    (hNextBoundary : cyclicOwnerCutIndex owner cut = cyclicSucc t) :
    ((Out).Incident (.inr (CoreActual first))
        (K.connector (trainCyclicPred t)) ∧
      (Out).Incident (.inr (CoreActual first)) (K.connector t)) ∧
    ((Out).Incident (.inr (CoreActual second)) (K.connector t) ∧
      (Out).Incident (.inr (CoreActual second))
        (K.connector (cyclicSucc t))) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨x, y, hPrev, hHere, _hFirst, _hSecond,
    _hDistinct, hParentFirst, hParentSecond,
    hFirstX, hSecondY, _hNoPair⟩ := hLong
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
  have hAtLeft :
      K.connector (trainCyclicPred t) = Sum.inl (CoreEmb x) := by
    have h := hMap (trainCyclicPred cut)
    rw [hPrev, hPrevBoundary] at h
    exact h.symm
  have hAtRight :
      K.connector (cyclicSucc t) = Sum.inl (CoreEmb y) := by
    have h := hMap cut
    rw [hHere, hNextBoundary] at h
    exact h.symm
  have hFirstLeft : (Out).Incident (.inr (CoreActual first))
      (K.connector (trainCyclicPred t)) := by
    rw [hAtLeft]
    change (CoreEmb x) ∈ (CoreActual first).1
    rw [actualAPictureEdgeEquiv_core_carrier
      A hA C.toRelStructure S R f first]
    exact ⟨x, hFirstX, rfl⟩
  have hFirstRight : (Out).Incident (.inr (CoreActual first))
      (K.connector t) := by
    rw [hOld]
    change CoreWagon ((Wit).parent first) = CoreWagon w
    exact congrArg CoreWagon hParentFirst
  have hSecondLeft : (Out).Incident (.inr (CoreActual second))
      (K.connector t) := by
    rw [hOld]
    change CoreWagon ((Wit).parent second) = CoreWagon w
    exact congrArg CoreWagon hParentSecond
  have hSecondRight : (Out).Incident (.inr (CoreActual second))
      (K.connector (cyclicSucc t)) := by
    rw [hAtRight]
    change (CoreEmb y) ∈ (CoreActual second).1
    rw [actualAPictureEdgeEquiv_core_carrier
      A hA C.toRelStructure S R f second]
    exact ⟨y, hSecondY, rfl⟩
  exact ⟨⟨hFirstLeft, hFirstRight⟩, ⟨hSecondLeft, hSecondRight⟩⟩

/-- For THREE OR MORE geometric owner cuts, every actual selected
non-singleton long piece of a supreme plan admits a globally legal
physical two-SHORT replacement around its old uncut wagon. The
replacement has the exact two-short literal word, is acceptable,
has unchanged twice-order, and preserves supreme pullback.

Strict geometric/designated rank descent is deliberately NOT claimed. -/
theorem attachedSelectedPicture_chosen_nonadjacent_long_two_short_complete
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n)
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
        ∃ t : Fin n, ∃ outLength : ℕ,
          ∃ H : (Out).BigCycle outLength,
            K.connector t = Sum.inr (CoreWagon w) ∧
            t ∉ cyclicOwnerCutPositions owner ∧
            List.ofFn (fun j : Fin outLength =>
              (H.label j, H.connector j)) =
              K.resultWord Out
                (K.twoConsecutiveShortPieces Out t
                  (CoreActual first) (CoreActual second)) ∧
            H.Acceptable ∧ H.twiceOrder = K.twiceOrder ∧
            (∀ kH : Fin outLength, H.HasSupremeAt Out kH →
              ∃ kK : Fin n, K.label kK = H.label kH ∧
                K.HasSupremeAt Out kK)) := by
  classical
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨pieces, hPlan, hProduces, hTwoStep⟩ :=
    attachedSelectedPicture_chosen_nonadjacent_long_exact_two_step
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hThreeCuts target cut hSupreme hNotForward
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
  obtain ⟨t, hOld, hUncut, hPrev, hNext⟩ :=
    hTwoStep first second w hp
  obtain ⟨hFirstInc, hSecondInc⟩ :=
    attachedSelectedPicture_long_piece_old_wagon_two_short_incidence
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target cut first second w hLong
      t hOld hPrev hNext
  obtain ⟨outLength, H, hWord, hOutAccept, hOrder, hPull⟩ :=
    K.twoConsecutiveShort_complete_of_three_le
      Out hAccept hLinear hn t
      (CoreActual first) (CoreActual second)
      hFirstInc hSecondInc
  exact ⟨t, outLength, H, hOld, hUncut,
    hWord, hOutAccept, hOrder, hPull⟩

end ActualChosenTwoStepShort
end StructuralRamsey.Girth

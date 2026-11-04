import Girth.TrainActualTwoShortOwnerTransport
import Girth.TrainActualChosenTwoStepShortComplete
import Girth.TrainActualLongStandardSupport
import Mathlib.Tactic

/-!
# Path A: chosen non-singleton long pieces yield actual nonincreasing-cut outputs

Combine the REAL selected reduced supreme plan's two-step old-wagon
classification with the actual physical two-short incidence, exact
short-only output labels, chosen-standard edge-carrier containment,
and minimum-geometric-owner construction.

Every chosen long piece at a non-singleton run, when the source has
three or more owner cuts, gives an actual acceptable output BigCycle
of the SAME Fin n, with the SAME connectors and twice-order,
supreme pullback, and MINIMUM GEOMETRIC OWNER CUT COUNT no larger
than that of the original owner word.

This is NOT a full lexicographic rank descent: unless at least one
replaced original label is designated or one cut strictly disappears,
strict decrease remains open. No appendix or manuscript marks.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ChosenTwoShortMinimumCuts

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

/-- A chosen long piece in a non-singleton owner run is replaced by
TWO actual physical short edges around the original wagon connector,
without increasing the minimum cyclic cut rank. This starts from the
genuine chosen plan, with no abstract output geometry hypothesis. -/
theorem attachedSelectedPicture_chosen_nonadjacent_long_two_short_minimum_cuts
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
    (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label target = Sum.inl i)
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
        ∃ t : Fin n, ∃ H : (Out).BigCycle n,
          K.connector t = Sum.inr (CoreWagon w) ∧
          t ∉ cyclicOwnerCutPositions owner ∧
          (∀ j : Fin n,
            H.label j = K.twoConsecutiveShortLabels Out t
              (CoreActual first) (CoreActual second) j) ∧
          (∀ j : Fin n, H.connector j = K.connector j) ∧
          H.Acceptable ∧ H.twiceOrder = K.twiceOrder ∧
          (∀ kH : Fin n, H.HasSupremeAt Out kH →
            ∃ kK : Fin n, K.label kK = H.label kH ∧
              K.HasSupremeAt Out kK) ∧
          ∃ minimumOwner : Fin n → I ⊕ CoreEdge,
            (∀ j, GeomAllowed (H.label j) (minimumOwner j)) ∧
            (∀ other : Fin n → I ⊕ CoreEdge,
              (∀ j, GeomAllowed (H.label j) (other j)) →
              cyclicOwnerChanges minimumOwner ≤ cyclicOwnerChanges other) ∧
            cyclicOwnerChanges minimumOwner ≤ cyclicOwnerChanges owner) := by
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
  obtain ⟨H, hLabels, hConnectors, hOutAccept, hOrder, hPull⟩ :=
    K.twoConsecutiveShort_complete_exact_labels
      Out hAccept hLinear hn t
      (CoreActual first) (CoreActual second)
      hFirstInc hSecondInc
  have hSupport :
      (CoreActual first).1 ⊆
        copyCarrier (RelStructure.Attachment.copyEmbedding C.toRelStructure S R f i) ∧
      (CoreActual second).1 ⊆
        copyCarrier (RelStructure.Attachment.copyEmbedding C.toRelStructure S R f i) :=
    sharedWitness_long_piece_physical_edges_in_standard
      A hA D C e R f U μ Z target cut first second w hLong i hTarget
  have hBefore : owner (trainCyclicPred t) ≠ owner t := by
    have hh := cyclicOwnerCutIndex_is_change owner (trainCyclicPred cut)
    rw [hPrev, cyclicSucc_trainCyclicPred_of_two_le
      (by omega : 2 ≤ n) t] at hh
    exact hh
  have hAfter : owner (cyclicSucc t) ≠
      owner (cyclicSucc (cyclicSucc t)) := by
    have hh := cyclicOwnerCutIndex_is_change owner cut
    rw [hNext] at hh
    exact hh
  obtain ⟨minimumOwner, hMinAllowed, hMin, hBound⟩ :=
    attachedSelectedPicture_two_short_minimum_cuts_le
      A hA B D C family selected e R f T U hShared μ
      K H hn owner hAllowed t i first second hLabels
      hSupport.1 hSupport.2 hBefore hAfter
  exact ⟨t, H, hOld, hUncut, hLabels, hConnectors,
    hOutAccept, hOrder, hPull,
    minimumOwner, hMinAllowed, hMin, hBound⟩

end ChosenTwoShortMinimumCuts
end StructuralRamsey.Girth

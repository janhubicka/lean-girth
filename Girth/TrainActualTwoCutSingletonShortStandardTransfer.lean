import Girth.TrainCyclicTwoCutSingletonComplement
import Girth.TrainActualPositiveCutShortPieceLift
import Girth.TrainActualPositiveCutStandardTransfer
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: genuine two-cut singleton short transfers to the original cycle

This is an ACTUAL attached-selected-picture supreme-transfer theorem,
not merely a reduced witness or local-piece statement.

Suppose exactly two geometric owner cuts exist, the run ending at
cut is a genuine singleton, and the OTHER reduced occurrence is a
chosen standard i with an actual reduced ShortValid edge b at cut.
The existing physical source lift gives both original connector
incidences of CoreActual b. The existing standard carrier lemma
locates the entire physical edge in standard i.

The two-cut singleton-complement lemma proves that EVERY kept
original source position has geometric owner i. The literal plan
SHORT at the singleton and KEEP everywhere else therefore satisfies
all hypotheses of the previously verified standard-replacement
supreme theorem: local incidence, no inserted long, vacuous long A2
and freshness, genuine target carrier support and actual kept-owner
equality. The old picture SupremeCycleBound then gives FULL
HasSimultaneousSupreme for the original source cycle.

No original designated B-label is equated to its owner; no extra
edge membership or AStrongness premise is postulated beyond those
required by the existing zero-cut transfer. This module does NOT
derive the choice of singleton cut or a short chosen standard from
the witness, solve the two-cut nonedge/long branch, or prove the
order-one mixed bridge case. No appendix or paper change.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutSingletonShortStandardTransfer

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
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Train" => generatedActualASupportTrain A hA
  C.toRelStructure S R f T U hShared
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- A real two-cut singleton SHORT, with chosen reduced target at the
OTHER cut, is enough to conclude global simultaneous supremeness of
the ORIGINAL cycle, with no guessed owner/source-label identity.

This discharges all physical standard-transfer obligations for that
case; only the existence and correctly oriented choice of the
reduced short remains a separate input. -/
theorem attachedSelectedPicture_two_cut_singleton_short_supreme_of_old_bound
    [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwoCopies : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n) (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwoCuts : cyclicOwnerChanges owner = 2)
    (cut : Fin (cyclicOwnerChanges owner))
    (hForward : cyclicOwnerCutIndex owner cut =
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut)))
    (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label (trainCyclicPred cut) = Sum.inl i)
    (b : CoreEdge)
    (hShort : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).ShortValid Wit
      (trainCyclicPred cut) cut b)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let pos : Fin n := cyclicOwnerCutIndex owner cut
  have hPrevious : cyclicOwnerCutIndex owner (trainCyclicPred cut) =
      trainCyclicPred pos := by
    dsimp [pos]
    rw [hForward]
    exact (trainCyclicPred_cyclicSucc_of_two_le (by omega : 2 ≤ n)
      (cyclicOwnerCutIndex owner (trainCyclicPred cut))).symm
  have hIncShort :
      (Out).Incident (.inr (CoreActual b))
        (K.connector (trainCyclicPred pos)) ∧
      (Out).Incident (.inr (CoreActual b)) (K.connector pos) :=
    attachedSelectedPicture_cut_short_piece_incident_lift
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts (trainCyclicPred cut) cut b
      hShort pos rfl hPrevious
  have hSupport : (CoreActual b).1 ⊆ copyCarrier (Std i) :=
    attachedSelectedPicture_cut_short_piece_carrier_in_standard
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts (trainCyclicPred cut) cut i
      hTarget b hShort
  have hOtherOwner :
      owner (cyclicOwnerCutIndex owner (trainCyclicPred cut)) =
        Sum.inl i := by
    change owner (cyclicOwnerCutIndex owner (trainCyclicPred cut)) =
      Sum.inl i at hTarget
    exact hTarget
  let pieces : Fin n → TrainSupremePiece ActualEdge
      (Quotient ((Train).wagonSetoid μ)) :=
    fun k => if k = pos then .short (CoreActual b) else .keep
  have hInc : K.LocalPieceIncidence Out pieces := by
    intro k
    by_cases hk : k = pos
    · subst k
      simpa [pieces, OrderOneData.BigCycle.LocalPieceIncidence]
        using hIncShort
    · simp [pieces, OrderOneData.BigCycle.LocalPieceIncidence, hk]
  have hNoLong : ∀ (k : Fin n) (a c : ActualEdge)
      (w : Quotient ((Train).wagonSetoid μ)),
      pieces k ≠ .long a w c := by
    intro k a c w
    by_cases hk : k = pos
    · simp [pieces, hk]
    · simp [pieces, hk]
  have hGeom : K.LocalLongA2Geometry Out pieces := by
    intro k a c w hp
    exact False.elim ((hNoLong k a c w) hp)
  have hFresh : ∀ (k : Fin n) (a : ActualEdge)
      (w : Quotient ((Train).wagonSetoid μ)) (c : ActualEdge),
      pieces k = .long a w c →
      ∀ t : Fin n, K.connector t ≠ Sum.inr w := by
    intro k a w c hp
    exact False.elim ((hNoLong k a c w) hp)
  have hKeep : ∀ k : Fin n, pieces k = .keep →
      owner k = Sum.inl i := by
    intro k hp
    by_cases hk : k = pos
    · subst k
      simp [pieces] at hp
    · have hOther := cyclicOwner_two_cut_singleton_complement_owner
        owner (by omega : 2 ≤ n) hTwoCuts cut hForward k hk
      exact hOther.trans hOtherOwner
  have hShortSupport : ∀ (k : Fin n) (a : ActualEdge),
      pieces k = .short a → a.1 ⊆ copyCarrier (Std i) := by
    intro k a hp
    by_cases hk : k = pos
    · subst k
      have hPiece :
          (TrainSupremePiece.short (CoreActual b) :
            TrainSupremePiece ActualEdge
              (Quotient ((Train).wagonSetoid μ))) =
            TrainSupremePiece.short a := by
        simpa [pieces] using hp
      have hb : CoreActual b = a := by
        injection hPiece with heq
        exact heq
      subst a
      exact hSupport
    · simp [pieces, hk] at hp
  have hLongSupport : ∀ (k : Fin n) (a : ActualEdge)
      (w : Quotient ((Train).wagonSetoid μ)) (c : ActualEdge),
      pieces k = .long a w c →
        a.1 ⊆ copyCarrier (Std i) ∧
        c.1 ⊆ copyCarrier (Std i) := by
    intro k a w c hp
    exact False.elim ((hNoLong k a c w) hp)
  exact attachedSelectedPicture_supreme_of_standard_replacement_of_three_le
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwoCopies hOldStrong hCoreStrong
    K hAccept hLinear hn hOrder owner hAllowed i pieces
    hInc hGeom hFresh hKeep hShortSupport hLongSupport hOldSupreme

end ActualTwoCutSingletonShortStandardTransfer
end StructuralRamsey.Girth

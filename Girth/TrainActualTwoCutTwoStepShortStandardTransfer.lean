import Girth.TrainCyclicTwoCutTwoStepComplement
import Girth.TrainActualPositiveCutStandardTransfer
import Girth.TrainTwoConsecutiveShortComplete
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: the original two-cut old-wagon two-short standard transfer

At EXACTLY TWO geometric owner cuts, suppose a non-target owner
run has the genuine two-step geometry pred(t), t, succ(t), with
the two boundary cuts pred(t), succ(t). Two physical output A-edges
first and second meeting the consecutive original source
connector pairs give an actual two-short replacement, retaining
the existing middle connector. The real two-cut run-fibre lemma
says that these are the ONLY positions of that owner run.

If both edges lie in the SAME other actual attached standard i,
every untouched source occurrence is owned by i. Thus the checked
global standard-local arbitrary replacement theorem applies:
  * local physical incidence is the genuine two-short geometry;
  * no new wagon is inserted, so long A2 and freshness are vacuous;
  * every kept original label belongs to the chosen geometric owner;
  * the two new actual physical edges lie inside the chosen standard;
  * the old-picture SupremeCycleBound supplies a complete global
    supreme plan at the EXACT original twice-order cutoff.

No original B-source label is identified with the chosen owner.
The theorem is a conditional physical transfer: it does not yet
construct the required two physical edges from a witness LONG,
locate the actual old wagon, or choose which of two standards
provides the pieces. Those are separate nonedge-branch obligations.
No appendix or circulation manuscript edits.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutTwoStepStandardTransfer

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
local notation "Selected" => {r : DesignatedCopy B D C family // r ∈ selected}
local notation "Train" => generatedActualASupportTrain A hA
  C.toRelStructure S R f T U hShared
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- The full ORIGINAL source cycle is globally supreme whenever a
genuine two-cut two-step owner run can be replaced by two consecutive
actual physical shorts contained in the opposite standard i.
This is the exact old-wagon transfer interface for the nonedge case:
the original wagon connector at t is retained, not reinserted. -/
theorem attachedSelectedPicture_two_cut_two_step_shorts_supreme_of_old_bound
    [Finite UA]
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n) (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hTwoCuts : cyclicOwnerChanges owner = 2)
    (cut : Fin (cyclicOwnerChanges owner))
    (t : Fin n)
    (hPrev : cyclicOwnerCutIndex owner (trainCyclicPred cut) =
      trainCyclicPred t)
    (hHere : cyclicOwnerCutIndex owner cut = cyclicSucc t)
    (i : I)
    (hTargetOwner :
      owner (cyclicOwnerCutIndex owner (trainCyclicPred cut)) =
        Sum.inl i)
    (first second : ActualEdge)
    (hFirst :
      (Out).Incident (.inr first) (K.connector (trainCyclicPred t)) ∧
      (Out).Incident (.inr first) (K.connector t))
    (hSecond :
      (Out).Incident (.inr second) (K.connector t) ∧
      (Out).Incident (.inr second) (K.connector (cyclicSucc t)))
    (hFirstSupport : first.1 ⊆ copyCarrier (Std i))
    (hSecondSupport : second.1 ⊆ copyCarrier (Std i))
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  let pieces : Fin n → TrainSupremePiece ActualEdge
      (Quotient ((Train).wagonSetoid μ)) :=
    K.twoConsecutiveShortPieces Out t first second
  have hNe : cyclicSucc t ≠ t :=
    cyclicSucc_ne_self_of_two_le (by omega : 2 ≤ n) t
  have hInc : K.LocalPieceIncidence Out pieces := by
    intro k
    by_cases hk : k = t
    · subst k
      simpa [pieces, OrderOneData.BigCycle.twoConsecutiveShortPieces,
        OrderOneData.BigCycle.LocalPieceIncidence] using hFirst
    · by_cases hs : k = cyclicSucc t
      · subst k
        have hPred : trainCyclicPred (cyclicSucc t) = t :=
          trainCyclicPred_cyclicSucc_of_two_le (by omega : 2 ≤ n) t
        simpa [pieces, OrderOneData.BigCycle.twoConsecutiveShortPieces,
          OrderOneData.BigCycle.LocalPieceIncidence, hNe, hPred] using hSecond
      · simp [pieces, OrderOneData.BigCycle.twoConsecutiveShortPieces,
          OrderOneData.BigCycle.LocalPieceIncidence, hk, hs]
  have hNoLong : ∀ (k : Fin n) (a b : ActualEdge)
      (w : Quotient ((Train).wagonSetoid μ)),
      pieces k ≠ .long a w b := by
    intro k a b w
    by_cases hk : k = t
    · simp [pieces, OrderOneData.BigCycle.twoConsecutiveShortPieces, hk]
    · by_cases hs : k = cyclicSucc t
      · simp [pieces, OrderOneData.BigCycle.twoConsecutiveShortPieces,
          hNe, hk, hs]
      · simp [pieces, OrderOneData.BigCycle.twoConsecutiveShortPieces,
          hk, hs]
  have hGeom : K.LocalLongA2Geometry Out pieces := by
    intro k a b w hp
    exact False.elim ((hNoLong k a b w) hp)
  have hFresh : ∀ (k : Fin n) (a : ActualEdge)
      (w : Quotient ((Train).wagonSetoid μ)) (b : ActualEdge),
      pieces k = .long a w b →
      ∀ s : Fin n, K.connector s ≠ Sum.inr w := by
    intro k a w b hp
    exact False.elim ((hNoLong k a b w) hp)
  have hKeep : ∀ k : Fin n, pieces k = .keep →
      owner k = Sum.inl i := by
    intro k hp
    have hKt : k ≠ t := by
      intro h
      subst k
      simp [pieces, OrderOneData.BigCycle.twoConsecutiveShortPieces] at hp
    have hKs : k ≠ cyclicSucc t := by
      intro h
      subst k
      simp [pieces, OrderOneData.BigCycle.twoConsecutiveShortPieces, hNe] at hp
    exact (cyclicOwner_two_cut_two_step_complement_owner
      owner hn hTwoCuts cut t k hPrev hHere hKt hKs).trans hTargetOwner
  have hShortSupport : ∀ (k : Fin n) (a : ActualEdge),
      pieces k = .short a → a.1 ⊆ copyCarrier (Std i) := by
    intro k a hp
    by_cases hk : k = t
    · subst k
      have hPiece :
          (TrainSupremePiece.short first :
            TrainSupremePiece ActualEdge
              (Quotient ((Train).wagonSetoid μ))) =
            TrainSupremePiece.short a := by
        simpa [pieces, OrderOneData.BigCycle.twoConsecutiveShortPieces] using hp
      have heq : first = a := by
        injection hPiece with heq
      subst a
      exact hFirstSupport
    · by_cases hs : k = cyclicSucc t
      · subst k
        have hPiece :
            (TrainSupremePiece.short second :
              TrainSupremePiece ActualEdge
                (Quotient ((Train).wagonSetoid μ))) =
              TrainSupremePiece.short a := by
          simpa [pieces, OrderOneData.BigCycle.twoConsecutiveShortPieces,
            hNe, hk] using hp
        have heq : second = a := by
          injection hPiece with heq
        subst a
        exact hSecondSupport
      · simp [pieces, OrderOneData.BigCycle.twoConsecutiveShortPieces,
          hk, hs] at hp
  have hLongSupport : ∀ (k : Fin n) (a : ActualEdge)
      (w : Quotient ((Train).wagonSetoid μ)) (b : ActualEdge),
      pieces k = .long a w b →
        a.1 ⊆ copyCarrier (Std i) ∧
        b.1 ⊆ copyCarrier (Std i) := by
    intro k a w b hp
    exact False.elim ((hNoLong k a b w) hp)
  exact attachedSelectedPicture_supreme_of_standard_replacement_of_three_le
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwoCopies hOldStrong hCoreStrong
    K hAccept hLinear hn hOrder owner hAllowed i pieces
    hInc hGeom hFresh hKeep hShortSupport hLongSupport hOldSupreme

end ActualTwoCutTwoStepStandardTransfer
end StructuralRamsey.Girth

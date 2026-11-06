import Girth.TrainActualExpandedPlanLocalIncidence
import Girth.TrainActualExpandedLongGeometry
import Girth.TrainActualExpandedTargetSupport
import Girth.TrainActualExpandedPlanKeepOwner
import Girth.TrainActualPositiveCutStandardTransfer
import Mathlib.Tactic

/-!
# Path A: one-pass positive-cut transfer with at least three original owner cuts

This theorem composes the ACTUAL one-pass source-indexed expansion of
one globally legal REDUCED supreme plan with the checked standard-
contained replacement transfer.

The proof no longer uses a strict decrease of cyclic geometric owner
cuts or designated occurrence count. All non-target runs have width
one or two under original A2/A3, and the selected reduced witness is
expanded SIMULTANEOUSLY to the original source cycle:
  * kept runs remain in the selected standard;
  * physical shorts and both edges of any physical long lie there;
  * every expanded source piece has correct original physical incidence;
  * original long A2 geometry is preserved by active AStrong gluing;
  * fresh long wagons are absent from all original source connectors.

The already checked standard-transfer theorem then constructs an
acceptable actual output, applies the zero-cut OLD supreme bound, and
pulls simultaneous supremeness back to the original output cycle.

All parent lemmas must compile at their exact heads before this
composition can be claimed as verified. The TWO-CUT/ORDER-ONE
branch and any subsequent forest lemma application remain separate.
No appendix or circulation manuscript changes.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualThreeCutOnePassStandardTransfer

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
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
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

local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

/-- Provided the REDUCED geometric cut witness has one genuine globally
legal supreme plan at a chosen STANDARD target i, an acceptable actual
output source cycle with >=3 geometric owner cuts has simultaneous
supremeness at the ORIGINAL twice-order cutoff.

The proof invokes only physically checked source replacements, never
assumes that a reduced geometric owner label is an original designated
source-copy label, and never rechooses the reduced plan.

The original selected-piece old bound and A-strongness hypotheses are
stated explicitly, as required by the checked zero-cut theorem. -/
theorem attachedSelectedPicture_three_cut_one_pass_supreme_of_old_bound
    [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n) (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (target : Fin (cyclicOwnerChanges owner)) (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label target = Sum.inl i)
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).HasSupremeAt Wit target)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨_hChosen, pieces, hPlan, outputLength,
    reducedOutput, hWord⟩ := hSupreme
  have hProduces : Z.PlanProducesBigCycle Wit pieces :=
    ⟨outputLength, reducedOutput, hWord⟩
  let expanded := cyclicExpandReducedPieces owner
    (by omega : 0 < cyclicOwnerChanges owner)
    pieces CoreActual CoreWagon
  have hInc : K.LocalPieceIncidence Out expanded :=
    attachedSelectedPicture_expanded_plan_localPieceIncidence
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept hn owner hAllowed hThree hOldStrong
      target pieces hPlan hProduces
  have hGeom : K.LocalLongA2Geometry Out expanded :=
    attachedSelectedPicture_expanded_plan_localLongA2Geometry
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hOldStrong
      target pieces hPlan
  have hFresh : ∀ (k : Fin n) (a : ActualEdge)
      (w : Quotient ((Train).wagonSetoid μ)) (b : ActualEdge),
      expanded k = .long a w b →
      ∀ t : Fin n, K.connector t ≠ Sum.inr w :=
    attachedSelectedPicture_expanded_plan_long_fresh
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept hn owner hAllowed hThree hOldStrong
      target pieces hPlan hProduces
  have hKeep : ∀ k : Fin n, expanded k = .keep →
      owner k = Sum.inl i :=
    attachedSelectedPicture_expanded_plan_keep_owned_by_target
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target i hTarget pieces hPlan
  obtain ⟨hShort, hLong⟩ :=
    attachedSelectedPicture_expanded_plan_edges_in_target_standard
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target i hTarget pieces hPlan
  exact attachedSelectedPicture_supreme_of_standard_replacement_of_three_le
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwo hOldStrong hCoreStrong
    K hAccept hLinear hn hOrder
    owner hAllowed i expanded
    hInc hGeom hFresh hKeep hShort hLong hOldSupreme

end ActualThreeCutOnePassStandardTransfer
end StructuralRamsey.Girth

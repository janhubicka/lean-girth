import Girth.TrainActualTwoCutLongFreshOldContacts
import Girth.TrainTwoStandardNoPairCommonLong
import Girth.TrainActualTwoCutFreshLongStandardTransfer
import Girth.TrainActualTwoCutTwoStepShortStandardTransfer
import Girth.TrainActualLongChosenStandardCarriers
import Girth.TrainActualChosenTwoStepShortComplete
import Girth.TrainActualPositiveCutLongPhysicalLift
import Girth.TrainCyclicTwoCutSingletonComplement
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: close original two-cut source from long pieces at both targets

If the ACTUAL cut-reduced BigCycle has exactly two designated standards
and a genuine LongValid at EACH possible non-target cut using the SAME
physical witness wagon w, then the original source cycle is globally
supreme under the ordinary old bound and strongness hypotheses.

The checked actual source A2/A3 splits contacts into fresh adjacent
or old straddling. In the fresh case one chooses the singleton original
owner run; the specified reduced long at that index yields the literal
physical one-long insertion, source-owner complement, true wagon
freshness and chosen-standard full-edge containment. In the old case
the checked two-cut wagon orientation gives the exact two-step source
run; the specified reduced long there provides two ACTUAL physical
short incidences around its existing wagon, again contained in the
opposite standard. Both invoke previously checked global standard
transfer and return original K.HasSimultaneousSupreme.

This theorem does NOT assume a pre-existing original supreme plan,
identify source B-labels with owner labels, or prune wagon classes.
The existence of a common-wagon reduced long for both standards
from witness FullSystemGirthGT is separately proved in
TrainTwoStandardNoPairCommonLong. Circulation only, no appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutNoPairLongSource

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

local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

include hRel


/-- An actual selected picture with exactly two owner cuts and
LongValid in BOTH possible reduced standard directions is fully
supreme on the ORIGINAL cycle, provided the long pieces use ONE
common witness wagon and the old picture has its supreme bound.

No fictitious original source label is selected. In particular
the old-wagon case uses real two-short physical output labels and
the fresh-wagon case uses a real one-long physical insertion. -/
theorem attachedSelectedPicture_two_cut_symmetric_long_full_supreme
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
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (hStandards : ∀ cut : Fin (cyclicOwnerChanges owner),
      ∃ i : I,
        (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed (by omega)).label cut = Sum.inl i)
    (w : Quotient (U.wagonSetoid μ))
    (hEveryLong : ∀ cut : Fin (cyclicOwnerChanges owner),
      ∃ first second : CoreEdge,
        (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed (by omega)).LongValid Wit
          (trainCyclicPred cut) cut first w second)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  let c0 : Fin (cyclicOwnerChanges owner) := ⟨0, by omega⟩
  obtain ⟨a0, b0, hLong0⟩ := hEveryLong c0
  rcases attachedSelectedPicture_two_cut_long_fresh_or_old_oriented
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept hn owner hAllowed hTwo
      (trainCyclicPred c0) c0 a0 b0 w hLong0
      with hFresh | hOld
  · obtain ⟨hFreshW, hAdjacent⟩ := hFresh
    have hSingleton : ∃ cut : Fin (cyclicOwnerChanges owner),
        cyclicOwnerCutIndex owner cut =
          cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut)) := by
      rcases hAdjacent with hf | hr
      · exact ⟨c0, hf⟩
      · refine ⟨trainCyclicPred c0, ?_⟩
        have hDouble : trainCyclicPred (trainCyclicPred c0) = c0 :=
          trainCyclicPred_pred_eq_self_of_card_two hTwo c0
        rw [hDouble]
        exact hr
    obtain ⟨cut, hForward⟩ := hSingleton
    obtain ⟨i, hTarget⟩ := hStandards (trainCyclicPred cut)
    obtain ⟨first, second, hLong⟩ := hEveryLong cut
    let pos : Fin n := cyclicOwnerCutIndex owner cut
    have hPrevious :
        cyclicOwnerCutIndex owner (trainCyclicPred cut) =
          trainCyclicPred pos := by
      dsimp [pos]
      rw [hForward]
      exact (trainCyclicPred_cyclicSucc_of_two_le
        (by omega : 2 ≤ n)
        (cyclicOwnerCutIndex owner (trainCyclicPred cut))).symm
    have hPhysical : K.PhysicalLongGeometry Out pos
        (CoreActual first) (CoreWagon w) (CoreActual second) :=
      attachedSelectedPicture_reduced_long_piece_physical_output
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts hOldStrong
        (trainCyclicPred cut) cut first second w hLong
        pos rfl hPrevious
    obtain ⟨hFirstStd, hSecondStd⟩ :=
      attachedSelectedPicture_long_piece_carriers_in_standard
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts
        (trainCyclicPred cut) cut i hTarget
        first second w hLong
    have hTargetOwner :
        owner (cyclicOwnerCutIndex owner (trainCyclicPred cut)) =
          Sum.inl i := by
      change owner (cyclicOwnerCutIndex owner (trainCyclicPred cut)) =
        Sum.inl i at hTarget
      exact hTarget
    have hKeepOwner : ∀ k : Fin n, k ≠ pos →
        owner k = Sum.inl i := by
      intro k hk
      have hh := cyclicOwner_two_cut_singleton_complement_owner
        owner (by omega : 2 ≤ n) hTwo cut hForward k hk
      exact hh.trans hTargetOwner
    exact attachedSelectedPicture_two_cut_fresh_singleton_long_supreme
      A hA B D C family selected e R f T U hShared hRel μ
      hStrong hTwoCopies hOldStrong hCoreStrong
      K hAccept hLinear hn hOrder
      owner hAllowed hTwo cut hForward i hKeepOwner
      (CoreActual first) (CoreActual second) (CoreWagon w)
      hPhysical hFreshW hFirstStd hSecondStd hOldSupreme
  · obtain ⟨t, hOldWagon, cut, hHere, hPrev, _hComplement⟩ := hOld
    obtain ⟨i, hTarget⟩ := hStandards (trainCyclicPred cut)
    obtain ⟨first, second, hLong⟩ := hEveryLong cut
    have hInc :=
      attachedSelectedPicture_long_piece_old_wagon_two_short_incidence
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts
        (trainCyclicPred cut) cut first second w hLong
        t hOldWagon hPrev hHere
    obtain ⟨hFirstStd, hSecondStd⟩ :=
      attachedSelectedPicture_long_piece_carriers_in_standard
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts
        (trainCyclicPred cut) cut i hTarget first second w hLong
    have hTargetOwner :
        owner (cyclicOwnerCutIndex owner (trainCyclicPred cut)) =
          Sum.inl i := by
      change owner (cyclicOwnerCutIndex owner (trainCyclicPred cut)) =
        Sum.inl i at hTarget
      exact hTarget
    exact attachedSelectedPicture_two_cut_two_step_shorts_supreme_of_old_bound
      A hA B D C family selected e R f T U hShared hRel μ
      hStrong hTwoCopies hOldStrong hCoreStrong
      K hAccept hLinear hn hOrder
      owner hAllowed hTwo cut t hPrev hHere i hTargetOwner
      (CoreActual first) (CoreActual second)
      hInc.1 hInc.2 hFirstStd hSecondStd hOldSupreme


/-- The FULL exactly-two-cut, two-STANDARD, two-VERTEX nonedge case
of original attached-output supreme-cycle transfer. The ordinary
witness FullSystemGirthGT q (q automatically >= 2 by source length
and order budget) produces one actual common wagon and LongValid
at BOTH target orientations. The complete fresh/old wagon physical
argument above then proves global HasSimultaneousSupreme of K.

No chosen reduced LongValid witness is assumed separately, and no
original designated B-label is identified with its geometric owner. -/
theorem attachedSelectedPicture_two_cut_noPair_full_supreme
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
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (i j : I)
    (hLabel0 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label ⟨0, by omega⟩ = Sum.inl i)
    (hLabel1 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label ⟨1, by omega⟩ = Sum.inl j)
    (x y : Y)
    (hConnector0 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).connector ⟨0, by omega⟩ = Sum.inl x)
    (hConnector1 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).connector ⟨1, by omega⟩ = Sum.inl y)
    (hNoPair : ¬ (Wit).PairEdge x y)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  have hLength : n ≤ K.twiceOrder :=
    OrderOneData.BigCycle.length_le_twiceOrder Out K
  have hq : 2 ≤ q := by omega
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨w, hEveryLong⟩ :=
    OrderOneData.BigCycle.two_standard_no_pair_long_each_cut_of_two
      Wit hTwo Z q hq hWitness i j
      hLabel0 hLabel1 x y hConnector0 hConnector1 hNoPair
  have hStandards : ∀ cut : Fin (cyclicOwnerChanges owner),
      ∃ s : I, Z.label cut = Sum.inl s := by
    intro cut
    have hk : cut.val = 0 ∨ cut.val = 1 := by
      have hb := cut.isLt
      omega
    rcases hk with hZero | hOne
    · have hIndex : cut =
          (⟨0, by omega⟩ : Fin (cyclicOwnerChanges owner)) :=
        Fin.ext hZero
      rw [hIndex]
      exact ⟨i, hLabel0⟩
    · have hIndex : cut =
          (⟨1, by omega⟩ : Fin (cyclicOwnerChanges owner)) :=
        Fin.ext hOne
      rw [hIndex]
      exact ⟨j, hLabel1⟩
  exact attachedSelectedPicture_two_cut_symmetric_long_full_supreme
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwoCopies hOldStrong hCoreStrong
    K hAccept hLinear hn hOrder owner hAllowed hTwo
    hStandards w hEveryLong hOldSupreme

end ActualTwoCutNoPairLongSource
end StructuralRamsey.Girth

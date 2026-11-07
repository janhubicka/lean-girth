import Girth.TrainCyclicTwoCutTwoStepComplement
import Girth.TrainActualPositiveCutStandardTransfer
import Girth.TrainOneFreshLongPhysical
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: fresh-wagon one-long source replacement at exactly two owner cuts

When an original acceptable selected attached output cycle has exactly
two geometric owner cuts, suppose one source owner run is a SINGLETON
at original source position pos, and the OTHER run is owned by the
chosen actual attached standard i. A physical fresh long insertion
(first, w, second) at pos has:
 * genuinely distinct output A-support edges of parent wagon w;
 * the correct two ORIGINAL vertex boundary connector incidences;
 * no ambient pair edge joining those two boundary vertices;
 * wagon w absent from EVERY original source connector.

The checked one-long physical incidence/A2/freshness constructors give
a globally legal arbitrary-replacement output. The owner-complement conclusion is supplied as the explicit
hKeepOwner premise (its derivation from two-cut singleton geometry
is checked separately in Path A #906), while both new physical
edges are explicitly contained in the chosen standard. The checked zero-cut old-bound
transfer therefore supplies complete ORIGINAL simultaneous
supremeness, at unchanged twice-order.

This theorem is the physical destination for the FRESH side of the
two-cut reduced LongValid source-contact dichotomy. It does NOT
produce a fresh long physical piece or its chosen standard from
reduced witness data; that last existence/orientation argument is
still separate. No original B-label identity, support pruning,
appendix or circulation manuscript change.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutFreshLongStandardTransfer

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

/-- An actual source SINGLETON long with physically fresh wagon,
both actual A-edges inside the other chosen standard, and the
genuine old-picture bound gives full ORIGINAL simultaneous supreme
at exactly two owner cuts. No source designated B-label is assumed. -/
theorem attachedSelectedPicture_two_cut_fresh_singleton_long_supreme
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
    (hForward : cyclicOwnerCutIndex owner cut =
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut)))
    (i : I)
    (hKeepOwner : ∀ k : Fin n,
      k ≠ cyclicOwnerCutIndex owner cut → owner k = Sum.inl i)
    (first second : ActualEdge)
    (w : Quotient ((Train).wagonSetoid μ))
    (hPhysical : K.PhysicalLongGeometry Out
      (cyclicOwnerCutIndex owner cut) first w second)
    (hFresh : ∀ t : Fin n, K.connector t ≠ Sum.inr w)
    (hFirstSupport : first.1 ⊆ copyCarrier (Std i))
    (hSecondSupport : second.1 ⊆ copyCarrier (Std i))
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  let pos : Fin n := cyclicOwnerCutIndex owner cut
  let pieces : Fin n → TrainSupremePiece ActualEdge
      (Quotient ((Train).wagonSetoid μ)) :=
    K.onlyLongPieces Out pos first w second
  have hInc : K.LocalPieceIncidence Out pieces :=
    K.onlyLongPieces_physical_incidence
      Out pos first w second hPhysical
  have hGeom : K.LocalLongA2Geometry Out pieces :=
    K.onlyLongPieces_physical_A2Geometry
      Out pos first w second hPhysical
  have hFreshPlan : ∀ (k : Fin n) (a : ActualEdge)
      (ww : Quotient ((Train).wagonSetoid μ)) (b : ActualEdge),
      pieces k = .long a ww b →
      ∀ s : Fin n, K.connector s ≠ Sum.inr ww :=
    K.onlyLongPieces_fresh Out pos first w second hFresh
  have hKeep : ∀ k : Fin n, pieces k = .keep →
      owner k = Sum.inl i := by
    intro k hp
    by_cases hk : k = pos
    · subst k
      simp [pieces, OrderOneData.BigCycle.onlyLongPieces] at hp
    · exact hKeepOwner k hk
  have hShortSupport : ∀ (k : Fin n) (a : ActualEdge),
      pieces k = .short a → a.1 ⊆ copyCarrier (Std i) := by
    intro k a hp
    by_cases hk : k = pos
    · subst k
      simp [pieces, OrderOneData.BigCycle.onlyLongPieces] at hp
    · simp [pieces, OrderOneData.BigCycle.onlyLongPieces, hk] at hp
  have hLongSupport : ∀ (k : Fin n) (a : ActualEdge)
      (ww : Quotient ((Train).wagonSetoid μ)) (b : ActualEdge),
      pieces k = .long a ww b →
        a.1 ⊆ copyCarrier (Std i) ∧
        b.1 ⊆ copyCarrier (Std i) := by
    intro k a ww b hp
    by_cases hk : k = pos
    · subst k
      have hPiece :
          (TrainSupremePiece.long first w second :
            TrainSupremePiece ActualEdge
              (Quotient ((Train).wagonSetoid μ))) =
            TrainSupremePiece.long a ww b := by
        simpa [pieces, OrderOneData.BigCycle.onlyLongPieces] using hp
      injection hPiece with hA hW hB
      subst a
      subst ww
      subst b
      exact ⟨hFirstSupport, hSecondSupport⟩
    · simp [pieces, OrderOneData.BigCycle.onlyLongPieces, hk] at hp
  exact attachedSelectedPicture_supreme_of_standard_replacement_of_three_le
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwoCopies hOldStrong hCoreStrong
    K hAccept hLinear hn hOrder owner hAllowed i pieces
    hInc hGeom hFreshPlan hKeep hShortSupport hLongSupport hOldSupreme

end ActualTwoCutFreshLongStandardTransfer
end StructuralRamsey.Girth

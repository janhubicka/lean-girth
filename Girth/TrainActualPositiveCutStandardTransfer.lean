import Girth.TrainActualPositiveCutPieceCarriers
import Girth.TrainActualZeroCutGlobalSupreme

/-!
# Track A: actual positive-cut transfer via an attached standard

This is the physical gluing counterpart of arbitrary supreme pullback.
Once a choice of replacement pieces for an acceptable output cycle is
provided, we use the *real* geometric-owner carrier theorem to place
the new cycle in one standard; the checked zero-cut theorem applies the
old selected-picture bound there, and the checked arbitrary-replacement
theorem pulls the resulting designated supremeness back.

The constructor of those pieces (especially minimum-segmentation
bridges), output linearity and the order-one boundary are still open.
No reduced witness copy is identified with an original designated
label, and no additional assumed local supreme bound is introduced.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualPositiveCutStandardTransfer

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

/-- If genuinely incident, A2-compatible, fresh arbitrary replacement
pieces into ONE chosen actual standard are supplied, then its old
supreme cycle bound proves simultaneous supremeness of the ORIGINAL
output cycle, at exactly the original twice-order.

Unlike a generic conditional transfer, this theorem *constructs* the
standard-local old-bound application using the verified actual
zero-cut theorem; the still-missing positive-cut input is explicitly
the physical choice of pieces satisfying the hypotheses. -/
theorem attachedSelectedPicture_supreme_of_standard_replacement_of_three_le
    [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n)
    (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (i : I)
    (pieces : Fin n → TrainSupremePiece ActualEdge
      (Quotient ((Train).wagonSetoid μ)))
    (hInc : K.LocalPieceIncidence Out pieces)
    (hGeom : K.LocalLongA2Geometry Out pieces)
    (hFresh : ∀ (k : Fin n) (a : ActualEdge)
      (w : Quotient ((Train).wagonSetoid μ)) (b : ActualEdge),
      pieces k = .long a w b →
      ∀ t : Fin n, K.connector t ≠ Sum.inr w)
    (hKeep : ∀ k : Fin n, pieces k = .keep → owner k = Sum.inl i)
    (hShort : ∀ (k : Fin n) (a : ActualEdge),
      pieces k = .short a → a.1 ⊆ copyCarrier (Std i))
    (hLong : ∀ (k : Fin n) (a : ActualEdge)
      (w : Quotient ((Train).wagonSetoid μ)) (b : ActualEdge),
      pieces k = .long a w b →
        a.1 ⊆ copyCarrier (Std i) ∧
        b.1 ⊆ copyCarrier (Std i))
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  obtain ⟨r, H, hWord, hAcceptH, hSameOrder, hPullback⟩ :=
    K.arbitrary_replacement_complete_of_three_le
      Out hAccept hLinear hn pieces hInc hGeom hFresh
  have hInStandard :
      ∀ k : Fin r, (Out).carrier (H.label k) ⊆
        copyCarrier (Std i) :=
    attachedSelectedPicture_replacement_labels_in_standard
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed i pieces hKeep hShort hLong H hWord
  obtain ⟨newOwner, hNewAllowed, hZero⟩ :=
    attachedSelectedPicture_geometric_zero_of_one_standard
      A hA B D C family selected e R f T U hShared μ
      H i hInStandard
  have hHOrder : H.twiceOrder ≤ 2 * q := by
    rw [hSameOrder]
    exact hOrder
  have hHSupreme : H.HasSimultaneousSupreme :=
    attachedSelectedPicture_zero_cut_supreme_of_old_bound
      A hA B D C family selected e R f T U hShared hRel μ
      hStrong hTwo hOldStrong hCoreStrong
      H hAcceptH hOldSupreme hHOrder
      newOwner hNewAllowed hZero
  obtain ⟨kH, hkDesignated, hHPlan⟩ := hHSupreme
  obtain ⟨kK, _, hKSupreme⟩ :=
    hPullback kH ⟨hkDesignated, hHPlan⟩
  exact K.hasSimultaneousSupreme_of_hasSupremeAt
    Out kK hKSupreme

end ActualPositiveCutStandardTransfer
end StructuralRamsey.Girth

import Girth.TrainActualPositiveCutStandardTransfer
import Girth.TrainSelectedPictureLinearPretrain

/-!
# Positive-cut transfer without postulating output linearity

Track B has established full linearity of the actual generated output
from source old/core linearity, witness order-two local bound, and the
strongness of the whole attached pieces. Reuse this theorem when
applying the checked arbitrary replacement and zero-cut supreme
pullback of Track A.

The physical replacement pieces are still explicit hypotheses.
This theorem neither assumes output LinearPretrain nor constructs
the missing positive-cut bridges or order-one legal output.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section SourceLinearPositiveCut

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
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "ActualEdge" => OldACarrierEdge A Actual
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "CoreCar" => attachedCoreAEdgeCarrier A C.toRelStructure S R f
local notation "CoreWitness" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f) CoreCar
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- The actual positive-cut transfer in a one-standard-contained
arbitrary replacement does NOT require output linearity as an axiom.
It is discharged using Track B's checked complete generated geometry.

The input local bound is for the physically lifted shared witness;
no illicit replacement of it by bare Berge girth is performed. -/
theorem attachedSelectedPicture_supreme_of_standard_replacement_of_source_geometry
    [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    (hOldLinear : (Old).LinearPretrain)
    (hCoreLinear : (CoreWitness).LinearPretrain)
    (hCoreBound : (CoreWitness).LocalPieceSystemBound 2)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
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
  have hLinear : (Out).LinearPretrain :=
    (attachedSelectedPicture_linear_and_strong_of_gluing_geometry
      A hA B D C family selected e R f T U hShared μ hRel
      hOldLinear hCoreLinear hCoreBound hOldStrong hCoreStrong).1
  exact attachedSelectedPicture_supreme_of_standard_replacement_of_three_le
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwo hOldStrong hCoreStrong K hAccept hLinear
    hn hOrder owner hAllowed i pieces hInc hGeom hFresh
    hKeep hShort hLong hOldSupreme

end SourceLinearPositiveCut

end StructuralRamsey.Girth

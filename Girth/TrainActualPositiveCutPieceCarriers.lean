import Girth.TrainSelectedCycleGeometricWagon
import Girth.TrainPositiveCutLabelProvenance

/-!
# Track A: piecewise geometric containment in an ACTUAL attached standard

A geometric owner is allowed to be a standard even when the original
label comes from a different indexed designated copy. What matters
for the replacement is its physical carrier, not its original label.
This module turns verified geometric occurrence ownership into a
literal property of every replacement output label, including long-piece
first edges. It does not assert that replacement edges with the necessary
two boundary incidences exist, nor that the output has an old-cycle
pullback or has an old supreme bound.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section PositiveCutPhysicalStandardContainment

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
variable (μ : Fin (m + 1))

local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding) R f)
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- Actual geometric ownership localises every physical edge incident
with that occurrence. This includes foreign designated labels, since
their geometric containment is a carrier statement. -/
theorem attachedSelectedPicture_geometric_owner_edge_in_standard
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (i : I) (j : Fin n) (hOwner : owner j = Sum.inl i)
    (edge : ActualEdge)
    (hEdge : edge ∈ (Out).edges (K.label j)) :
    edge.1 ⊆ copyCarrier (Std i) := by
  have hLabel : (Out).carrier (K.label j) ⊆
      copyCarrier (Std i) := by
    have h := hAllowed j
    rw [hOwner] at h
    exact h
  exact (attachedSelectedPicture_edge_within_label_carrier
    A hA B D C family selected e R f T U hShared μ
    (K.label j) edge hEdge).trans hLabel

/-- All literal replacement output labels are geometrically inside
one ACTUAL standard if kept occurrences are assigned to that standard
and the chosen replacement edges are physically contained there.
The latter two premises are the precise remaining geometric choice
obligations; no original designated target is assumed. -/
theorem attachedSelectedPicture_replacement_labels_in_standard
    {n r : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (i : I)
    (pieces : Fin n → TrainSupremePiece ActualEdge
      (Quotient ((generatedActualASupportTrain A hA
        C.toRelStructure (activeCarrier A C e.toFunctionEmbedding)
        R f T U hShared).wagonSetoid μ)))
    (hKeep : ∀ j : Fin n,
      pieces j = .keep → owner j = Sum.inl i)
    (hShort : ∀ (j : Fin n) (edge : ActualEdge),
      pieces j = .short edge → edge.1 ⊆ copyCarrier (Std i))
    (hLong : ∀ (j : Fin n) (edge : ActualEdge)
      (w : Quotient ((generatedActualASupportTrain A hA
        C.toRelStructure (activeCarrier A C e.toFunctionEmbedding)
        R f T U hShared).wagonSetoid μ))
      (other : ActualEdge),
      pieces j = .long edge w other →
        edge.1 ⊆ copyCarrier (Std i) ∧
        other.1 ⊆ copyCarrier (Std i))
    (H : (Out).BigCycle r)
    (hWord : List.ofFn (fun k : Fin r =>
        (H.label k, H.connector k)) = K.resultWord Out pieces) :
    ∀ k : Fin r, (Out).carrier (H.label k) ⊆ copyCarrier (Std i) := by
  have hPieces : ∀ j : Fin n,
      match pieces j with
      | .keep => (Out).carrier (K.label j) ⊆ copyCarrier (Std i)
      | .short edge => (Out).carrier (Sum.inr edge) ⊆
          copyCarrier (Std i)
      | .long edge _ other =>
          (Out).carrier (Sum.inr edge) ⊆ copyCarrier (Std i) ∧
          (Out).carrier (Sum.inr other) ⊆ copyCarrier (Std i) := by
    intro j
    cases hp : pieces j with
    | keep =>
        have hOwner : owner j = Sum.inl i := hKeep j hp
        have hh := hAllowed j
        rw [hOwner] at hh
        exact hh
    | short edge =>
        change edge.1 ⊆ copyCarrier (Std i)
        exact hShort j edge hp
    | long edge w other =>
        change edge.1 ⊆ copyCarrier (Std i) ∧
          other.1 ⊆ copyCarrier (Std i)
        exact hLong j edge w other hp
  apply K.replacement_labels_of_piece_property
    Out H pieces (fun a => (Out).carrier a ⊆ copyCarrier (Std i))
  · intro j
    cases hp : pieces j with
    | keep =>
        simpa only [hp] using hPieces j
    | short edge =>
        simpa only [hp] using hPieces j
    | long edge w other =>
        simpa only [hp] using hPieces j
  · exact hWord

end PositiveCutPhysicalStandardContainment
end StructuralRamsey.Girth

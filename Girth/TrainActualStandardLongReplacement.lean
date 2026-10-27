import Girth.TrainActualStandardShortReplacement
import Girth.TrainActualSupportCarrierUniqueness

/-!
# Long supreme-replacement pieces in an attached standard

Short physical pieces lift without additional geometric assumptions.
For a LONG piece, the decisive extra fact is reflection of the
absence of a physical ambient pair edge between the two boundary
vertices. This module deliberately retains that fact as an EXPLICIT
hypothesis rather than silently deriving it from ordinary inducedness
of a relational embedding.

Given pair-edge reflection for the one standard, all remaining
requirements of LongValid transfer: genuine standard edge membership,
distinct physical support edges, their exact common wagon and both
boundary vertex incidences.

Proving pair-edge reflection from the partite picture's A-strong
geometry, and assembling a globally valid simultaneous replacement
word, remain open. No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section StandardLongReplacements

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
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "StdEdge" => fun (i : I) (old : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f) i old)
local notation "StdWagon" => generatedActualASupportTrain_standardWagonEmbedding
  A hA C.toRelStructure S R f T U hRel hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Within one standard, the actual A-edge carrier map is injective.
Actual support edges are SETS and not arbitrary embedding names. -/
theorem attachedSelectedPicture_standard_edge_injective (i : I) :
    Function.Injective (StdEdge i) := by
  intro a b h
  apply Subtype.ext
  have hCar : (StdEdge i a).1 = (StdEdge i b).1 :=
    congrArg Subtype.val h
  rw [actualAPictureEdgeEquiv_standard_carrier
        A hA C.toRelStructure S R f i a,
      actualAPictureEdgeEquiv_standard_carrier
        A hA C.toRelStructure S R f i b] at hCar
  change ((fun x : X => Std i x) '' a.1) =
    ((fun x : X => Std i x) '' b.1) at hCar
  exact (attachment_standardCarrier_image_eq_iff
    C.toRelStructure S R f i a.1 b.1).mp hCar

/-- A chosen valid LONG replacement lifts physically if every ambient
output A-edge through two vertices of the standard reflects to
a genuine old A-edge. This is the precise still-open strongness
interface, not a consequence claimed here. -/
theorem attachedSelectedPicture_standard_longValid_lift
    (i : I) {n : ℕ}
    (Z : (Old).BigCycle n) (K : (Out).BigCycle n)
    (hLabel : ∀ j : Fin n,
      LabelMap i (Z.label j) = K.label j)
    (hConnector : ∀ j : Fin n,
      Sum.map (Std i) (StdWagon i) (Z.connector j) = K.connector j)
    (hPairBack : ∀ x y : X,
      (Out).PairEdge (Std i x) (Std i y) → (Old).PairEdge x y)
    (k j : Fin n) (a b : OldEdge) (p : Quotient (T.wagonSetoid μ))
    (hLong : OrderOneData.BigCycle.LongValid (Old) Z k j a p b) :
    OrderOneData.BigCycle.LongValid
      (Out) K k j (StdEdge i a) (StdWagon i p) (StdEdge i b) := by
  obtain ⟨x, y, hLeft, hRight, ha, hb, hab, hap, hbp, hx, hy, hNoPair⟩ := hLong
  refine ⟨Std i x, Std i y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      K.connector (trainCyclicPred j) =
          Sum.map (Std i) (StdWagon i) (Z.connector (trainCyclicPred j)) :=
            (hConnector (trainCyclicPred j)).symm
      _ = Sum.inl (Std i x) := by rw [hLeft]; rfl
  · calc
      K.connector j =
          Sum.map (Std i) (StdWagon i) (Z.connector j) :=
            (hConnector j).symm
      _ = Sum.inl (Std i y) := by rw [hRight]; rfl
  · rw [← hLabel k]
    exact attachedSelectedPicture_standard_edge_membership_lift
      A hA B D C family selected e R f T U hShared hRel μ
      i (Z.label k) a ha
  · rw [← hLabel k]
    exact attachedSelectedPicture_standard_edge_membership_lift
      A hA B D C family selected e R f T U hShared hRel μ
      i (Z.label k) b hb
  · intro hEq
    exact hab (attachedSelectedPicture_standard_edge_injective
      A hA B D C family selected e R f T U hShared hRel μ i hEq)
  · change Quotient.mk ((Train).wagonSetoid μ) (StdEdge i a) =
      StdWagon i p
    calc
      _ = StdWagon i (Quotient.mk (T.wagonSetoid μ) a) :=
        (generatedActualASupportTrain_standardWagonEmbedding_mk
          A hA C.toRelStructure S R f T U hRel hShared μ i a).symm
      _ = StdWagon i p := congrArg (StdWagon i) hap
  · change Quotient.mk ((Train).wagonSetoid μ) (StdEdge i b) =
      StdWagon i p
    calc
      _ = StdWagon i (Quotient.mk (T.wagonSetoid μ) b) :=
        (generatedActualASupportTrain_standardWagonEmbedding_mk
          A hA C.toRelStructure S R f T U hRel hShared μ i b).symm
      _ = StdWagon i p := congrArg (StdWagon i) hbp
  · change Std i x ∈ (StdEdge i a).1
    rw [actualAPictureEdgeEquiv_standard_carrier
      A hA C.toRelStructure S R f i a]
    exact ⟨x, hx, rfl⟩
  · change Std i y ∈ (StdEdge i b).1
    rw [actualAPictureEdgeEquiv_standard_carrier
      A hA C.toRelStructure S R f i b]
    exact ⟨y, hy, rfl⟩
  · intro hOutputPair
    exact hNoPair (hPairBack x y hOutputPair)

end StandardLongReplacements
end StructuralRamsey.Girth

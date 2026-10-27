import Girth.TrainActualZeroCutAcceptable
import Girth.TrainSimultaneousSupreme

/-!
# Short replacement pieces in a genuine attached standard

The zero-cut cycle is already pulled back with exact labels and
connectors. A further obligation for lifting globally legal supreme
replacements is to transport every old short piece into the actual
output incidence system.

We prove it literally: an old edge belonging to a designated/physical
source label becomes an actual A-support edge of the same output label;
its vertex incidences and wagon-class incidence are preserved by the
real standard embeddings and the injective old-to-output wagon map.

No ambient pair-edge reflection (required for long pieces) and no
global simultaneous-replacement cycle are assumed or concluded.
No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section StandardShortReplacements

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
local notation "Label" => {q : DesignatedCopy B D C family // q ∈ selected} ⊕ OldEdge
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

/-- A real old A-support edge belonging to an old designated or
physical edge label remains an actual output A-support edge of
the same labelled standard. No selected-copy substitution. -/
theorem attachedSelectedPicture_standard_edge_membership_lift
    (i : I) (a : Label) (old : OldEdge)
    (he : old ∈ (Old).edges a) :
    StdEdge i old ∈ (Out).edges (LabelMap i a) := by
  exact (attachedSelectedPicture_edges
    A hA B D C family selected e R f T U hShared μ
    i a (StdEdge i old)).mpr ⟨old, he, rfl⟩

/-- Both vertex and wagon incidences of a real old physical edge
remain true for its exact physical standard image. -/
theorem attachedSelectedPicture_standard_edge_incident_lift
    (i : I) (old : OldEdge)
    (q : X ⊕ Quotient (T.wagonSetoid μ))
    (h : (Old).Incident (Sum.inr old) q) :
    (Out).Incident (Sum.inr (StdEdge i old))
      (Sum.map (Std i) (StdWagon i) q) := by
  cases q with
  | inl x =>
      change x ∈ old.1 at h
      change Std i x ∈ (StdEdge i old).1
      rw [actualAPictureEdgeEquiv_standard_carrier
        A hA C.toRelStructure S R f i old]
      exact ⟨x, h, rfl⟩
  | inr p =>
      change (Old).Meets (Sum.inr old) p at h
      obtain ⟨b, hb, hp⟩ := h
      have hbo : b = old := hb
      subst b
      change (Out).Meets (Sum.inr (StdEdge i old)) (StdWagon i p)
      refine ⟨StdEdge i old, rfl, ?_⟩
      calc
        Quotient.mk ((Train).wagonSetoid μ) (StdEdge i old) =
          StdWagon i (Quotient.mk (T.wagonSetoid μ) old) :=
            (generatedActualASupportTrain_standardWagonEmbedding_mk
              A hA C.toRelStructure S R f T U hRel hShared μ i old).symm
        _ = StdWagon i p := congrArg (StdWagon i) hp

/-- The actual zero-cut standard image preserves a chosen valid
SHORT supreme-replacement piece with its two original boundary
connectors. This verifies local replacement data, not simultaneous
validity of a whole replacement word. -/
theorem attachedSelectedPicture_standard_shortValid_lift
    (i : I) {n : ℕ}
    (Z : (Old).BigCycle n) (K : (Out).BigCycle n)
    (hLabel : ∀ j : Fin n,
      LabelMap i (Z.label j) = K.label j)
    (hConnector : ∀ j : Fin n,
      Sum.map (Std i) (StdWagon i) (Z.connector j) = K.connector j)
    (k j : Fin n) (old : OldEdge)
    (hShort : OrderOneData.BigCycle.ShortValid (Old) Z k j old) :
    OrderOneData.BigCycle.ShortValid (Out) K k j (StdEdge i old) := by
  obtain ⟨hMember, hLeft, hRight⟩ := hShort
  refine ⟨?_, ?_, ?_⟩
  · rw [← hLabel k]
    exact attachedSelectedPicture_standard_edge_membership_lift
      A hA B D C family selected e R f T U hShared hRel μ i
      (Z.label k) old hMember
  · have hMapped :=
      attachedSelectedPicture_standard_edge_incident_lift
        A hA B D C family selected e R f T U hShared hRel μ
        i old (Z.connector (trainCyclicPred j)) hLeft
    rw [hConnector (trainCyclicPred j)] at hMapped
    exact hMapped
  · have hMapped :=
      attachedSelectedPicture_standard_edge_incident_lift
        A hA B D C family selected e R f T U hShared hRel μ
        i old (Z.connector j) hRight
    rw [hConnector j] at hMapped
    exact hMapped

end StandardShortReplacements
end StructuralRamsey.Girth

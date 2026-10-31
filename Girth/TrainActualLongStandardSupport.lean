import Girth.TrainActualOrderOneCutBridge

/-!
# Genuine reduced long pieces have TWO physical edges in the chosen standard

A long piece in an actual shared witness is supported by two DIFFERENT
core edges in the selected reduced label. If that label is a standard
index, both core edges come from genuine shared old support. Hence their
actual physical images are carried by the same attached standard.

This is not a first-stage source-labelled LongValid claim: the reduced
standard is not identified with any original designated B occurrence.
No owner-cut descent, insertion-position alignment, or new supreme
label is asserted. Circulation only.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualLongStandardSupport

variable {L : RelLanguage.{u}} {UA P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Wit" => sharedWitnessOrderOneData U μ Emb
  (Subtype.val : CoreEdge → Set Y)

/-- If an ACTUAL witness long piece is sourced from reduced standard i,
both (distinct) edges used by the piece have real physical carriers
contained in the SAME attached standard i. No original labelled
designated source occurrence is assumed. -/
theorem sharedWitness_long_piece_physical_edges_in_standard
    {n : ℕ} (Z : (Wit).BigCycle n)
    (target cut : Fin n)
    (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ))
    (hLong : Z.LongValid Wit target cut first w second)
    (i : I) (hTarget : Z.label target = Sum.inl i) :
    (CoreActual first).1 ⊆ copyCarrier (Std i) ∧
      (CoreActual second).1 ⊆ copyCarrier (Std i) := by
  obtain ⟨_x, _y, _hLeft, _hRight, hFirst, hSecond,
    _hNe, _hParentFirst, _hParentSecond, _hFirstX, _hSecondY,
    _hNoPair⟩ := hLong
  rw [hTarget] at hFirst hSecond
  change first ∈ Set.range (Emb i) at hFirst
  change second ∈ Set.range (Emb i) at hSecond
  obtain ⟨s, hs⟩ := hFirst
  obtain ⟨t, ht⟩ := hSecond
  constructor
  · rw [← hs]
    exact actualSharedCoreEdge_carrier_subset_standard
      A hA C.toRelStructure S R f i s
  · rw [← ht]
    exact actualSharedCoreEdge_carrier_subset_standard
      A hA C.toRelStructure S R f i t

end ActualLongStandardSupport
end StructuralRamsey.Girth

import Girth.TrainActualLengthTwoVertexPairStrongSupreme
import Girth.TrainSelectedPictureOutputIncidence
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual attached selected source: length-two vertex pair with a physical edge

The generic globally legal short-plan theorem only needs an honest
pair-edge closure for the designated copy. In the ACTUAL selected
picture, copyEdges is DEFINED by complete physical A-edge carrier
containment. Consequently the actual AStrong condition for every
transported selected copy supplies that closure without a new
abstract "copy-edge membership" assumption.

This theorem is conditional only on original length-two acceptability,
one genuine designated source occurrence, the complete selected
copy AStrong geometry, and an ACTUAL physical A-edge joining the two
vertex connectors. In particular it does NOT assume that the whole
attached output has FullSystemGirthGT or a SupremeCycleBound.

This is a precise physical kernel; the n=2 designated existence
is supplied separately by linearity and the remaining no-pair-edge
case has no short replacement of this form. No appendix.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
section ActualLengthTwoVertexPairStrong

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D) (R : RelStructure L Y)
variable (f : I → Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty
  (SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Attached" =>
  RelStructure.Attachment.attach C.toRelStructure S R f
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "ActualEdge" => OldACarrierEdge A Attached
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ

/-- A physical pair edge and actual A-strongness of the designated
selected output copies produce the COMPLETE original legal supreme
replacement at source length two. This does not assume output girth. -/
theorem attachedSelectedPicture_length_two_vertex_pairEdge_full_supreme
    (hSelectedStrong : ∀ iq : I × Selected,
      AStrong A Attached ((Out).copyCarrier iq))
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (hDesignated : ∃ k : Fin 2, (Out).designated (K.label k))
    (x y : Vertex)
    (hX : K.connector (0 : Fin 2) = Sum.inl x)
    (hY : K.connector (1 : Fin 2) = Sum.inl y)
    (b : ActualEdge) (hBx : x ∈ b.1) (hBy : y ∈ b.1) :
    K.HasSimultaneousSupreme := by
  apply OrderOneData.BigCycle.two_vertex_pairEdge_supreme_of_selectedStrong
    (Out) K hAccept x y hX hY b hBx hBy ?_ hDesignated
  intro iq edge u v huv hui hvi hue hve
  obtain ⟨a, ha⟩ := edge.2
  have huA : u ∈ copyCarrier a := by
    rw [← ha]
    exact hue
  have hvA : v ∈ copyCarrier a := by
    rw [← ha]
    exact hve
  have hLarge :
      ¬ (copyCarrier a ∩ (Out).copyCarrier iq).Subsingleton := by
    intro hSmall
    exact huv (hSmall ⟨huA, hui⟩ ⟨hvA, hvi⟩)
  have hSubset : copyCarrier a ⊆ (Out).copyCarrier iq :=
    hSelectedStrong iq a hLarge
  change edge.1 ⊆ (Out).copyCarrier iq
  rw [ha]
  exact hSubset

end ActualLengthTwoVertexPairStrong

end StructuralRamsey.Girth

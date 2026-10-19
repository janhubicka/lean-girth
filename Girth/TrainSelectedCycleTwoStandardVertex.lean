import Girth.TrainSelectedCycleVertexCoreBoundary

/-!
# Circulation: two-standard vertex boundaries of actual selected big cycles

An actual vertex connector between two selected labels in distinct
physical standard pictures belongs to both of those labelled carriers.
The already verified free-attachment intersection theorem then
identifies its unique core preimage and places it in BOTH prescribed
local witness copies. No additional global coverage hypothesis is
required, and no witness reduct or A1--A3 conclusion is asserted.

No appendix imports.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
section SelectedTwoStandardVertex

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

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Label" => Selected ⊕ OldACarrierEdge A C.toRelStructure
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f

/-- An actual selected BigCycle vertex boundary between distinct
physical standards is represented by one witness vertex lying inside
both corresponding local copies. The source-index distinction is
explicit and is NOT derived from minimality of an arbitrary word. -/
theorem attachedSelectedPicture_cycle_vertex_two_standard_local
    {n : ℕ} (K : (Out).BigCycle n)
    (k : Fin n) (x : Vertex) (i j : I) (a b : Label)
    (hij : i ≠ j)
    (hV : K.connector k = Sum.inl x)
    (ha : K.label k = LabelMap i a)
    (hb : K.label (cyclicSucc k) = LabelMap j b) :
    ∃ y : Y,
      CoreEmb y = x ∧
      y ∈ copyCarrier (f i) ∧
      y ∈ copyCarrier (f j) := by
  have hBoth :=
    OrderOneData.BigCycle.vertex_boundary_in_both_labels Out K k x hV
  have hxI : x ∈ copyCarrier (Std i) := by
    have hCarrier : x ∈ (Out).carrier (LabelMap i a) := by
      simpa only [ha] using hBoth.1
    rw [attachedSelectedPicture_carrier
      A hA B D C family selected e R f T U hShared μ i a] at hCarrier
    rcases hCarrier with ⟨z, _hz, hzx⟩
    exact ⟨z, hzx⟩
  have hxJ : x ∈ copyCarrier (Std j) := by
    have hCarrier : x ∈ (Out).carrier (LabelMap j b) := by
      simpa only [hb] using hBoth.2
    rw [attachedSelectedPicture_carrier
      A hA B D C family selected e R f T U hShared μ j b] at hCarrier
    rcases hCarrier with ⟨z, _hz, hzx⟩
    exact ⟨z, hzx⟩
  exact attachment_shared_point_in_both_local_images
    C.toRelStructure S R f hij hxI hxJ

end SelectedTwoStandardVertex

end StructuralRamsey.Girth

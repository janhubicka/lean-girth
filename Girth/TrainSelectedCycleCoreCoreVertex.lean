import Girth.TrainSelectedCycleVertexCoreBoundary

/-!
# Circulation: two singleton core edges at an actual vertex boundary

A genuine vertex connector between two singleton witness-core A-edge
labels is represented by the SAME witness vertex in both edges.
The conclusion uses literal BigCycle incidence and injectivity of
the attachment core embedding; it introduces no train-compatibility,
segment-minimality, or legal-reduct assumptions.

This is one local boundary case, not an A1--A3 transfer.
No appendix imports.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
section SelectedCoreCoreVertex

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
local notation "CoreEdge" => OldACarrierEdge A R
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ

/-- A physical vertex connector between two singleton core labels
identifies one common vertex of the two original witness A-edges. -/
theorem attachedSelectedPicture_cycle_vertex_core_core_local
    {n : ℕ} (K : (Out).BigCycle n)
    (k : Fin n) (x : Vertex) (b c : CoreEdge)
    (hx : K.connector k = Sum.inl x)
    (hLeft : K.label k = Sum.inr (CoreActual b))
    (hRight : K.label (cyclicSucc k) = Sum.inr (CoreActual c)) :
    ∃ y : Y, CoreEmb y = x ∧ y ∈ b.1 ∧ y ∈ c.1 := by
  have hBoth :=
    OrderOneData.BigCycle.vertex_boundary_in_both_labels Out K k x hx
  have hxB : x ∈ (CoreActual b).1 := by
    have hMem := hBoth.1
    rw [hLeft] at hMem
    change x ∈ (CoreActual b).1 at hMem
    exact hMem
  have hxC : x ∈ (CoreActual c).1 := by
    have hMem := hBoth.2
    rw [hRight] at hMem
    change x ∈ (CoreActual c).1 at hMem
    exact hMem
  rw [actualAPictureEdgeEquiv_core_carrier
    A hA C.toRelStructure S R f b] at hxB
  rw [actualAPictureEdgeEquiv_core_carrier
    A hA C.toRelStructure S R f c] at hxC
  change x ∈ (fun y : Y => CoreEmb y) '' b.1 at hxB
  change x ∈ (fun y : Y => CoreEmb y) '' c.1 at hxC
  obtain ⟨y, hy, hyx⟩ := hxB
  obtain ⟨z, hz, hzx⟩ := hxC
  have hyz : y = z := (CoreEmb).injective (hyx.trans hzx.symm)
  have hyC : y ∈ c.1 := by simpa only [hyz] using hz
  exact ⟨y, hyx, hy, hyC⟩

end SelectedCoreCoreVertex

end StructuralRamsey.Girth

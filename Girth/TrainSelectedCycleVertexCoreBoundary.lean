import Girth.TrainSelectedCycleBoundaryIncidence
import Girth.AttachmentGeometry
import Girth.TrainActualPhysicalEdgeCarrierEval

/-!
# Circulation: vertex boundary of a standard and a singleton core edge

An actual selected-picture BigCycle vertex connector adjacent to an
indexed standard label and a genuine singleton core A-edge is a REAL
core vertex. The attachment intersection theorem places that vertex
in the local witness copy Q_i; incidence with the singleton edge is
retained as an independent, stronger assertion.

This is one geometric boundary case for the minimum-segmentation
reduct. No cyclic reduct or A1--A3 property is asserted. No appendix.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section SelectedVertexCoreBoundary

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
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Label" => Selected ⊕ OldEdge
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f

/-- A vertex connector between a designated/edge occurrence from
standard i and an actual singleton core edge b comes from a witness
vertex in Q_i AND in b. The original physical vertex is its unique
core image. -/
theorem attachedSelectedPicture_cycle_vertex_standard_core_local
    {n : ℕ} (K : (Out).BigCycle n)
    (k : Fin n) (x : Vertex) (i : I)
    (a : Label) (b : CoreEdge)
    (hx : K.connector k = Sum.inl x)
    (hLeft : K.label k = LabelMap i a)
    (hRight : K.label (cyclicSucc k) = Sum.inr (CoreActual b)) :
    ∃ y : Y,
      CoreEmb y = x ∧ y ∈ copyCarrier (f i) ∧ y ∈ b.1 := by
  have hBoth :=
    OrderOneData.BigCycle.vertex_boundary_in_both_labels
      Out K k x hx
  have hxStandard :
      x ∈ copyCarrier (Std i) := by
    have hCarrierA : x ∈ (Out).carrier (LabelMap i a) := by
      simpa only [hLeft] using hBoth.1
    rw [attachedSelectedPicture_carrier
      A hA B D C family selected e R f T U hShared μ i a] at hCarrierA
    rcases hCarrierA with ⟨z, _hz, hzx⟩
    exact ⟨z, hzx⟩
  have hxCoreEdge : x ∈ (CoreActual b).1 := by
    have hRightMem := hBoth.2
    rw [hRight] at hRightMem
    change x ∈ (CoreActual b).1 at hRightMem
    exact hRightMem
  rw [actualAPictureEdgeEquiv_core_carrier
    A hA C.toRelStructure S R f b] at hxCoreEdge
  change x ∈ (fun y : Y => CoreEmb y) '' b.1 at hxCoreEdge
  obtain ⟨y, hy, hyx⟩ := hxCoreEdge
  have hxCore : x ∈ copyCarrier CoreEmb := ⟨y, hyx⟩
  have hxLocal : x ∈ copyCarrier ((CoreEmb).comp (f i)) := by
    rw [← attachment_copy_core_intersection
      C.toRelStructure S R f i]
    exact ⟨hxStandard, hxCore⟩
  obtain ⟨t, htx⟩ := hxLocal
  have hyt : y = f i t := (CoreEmb).injective (hyx.trans htx.symm)
  exact ⟨y, hyx, ⟨t, hyt.symm⟩, hy⟩

end SelectedVertexCoreBoundary

end StructuralRamsey.Girth

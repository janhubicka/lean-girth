import Girth.TrainCyclicOwnerAbsorption
import Girth.TrainSelectedCycleTwoStandardVertex
import Girth.TrainSelectedCycleCoreCoreVertex

/-!
# Circulation: actual vertex boundaries between GEOMETRIC segment owners

The earlier physical boundary lemmas checked actual selected output
labels only when they were presented as literal standard-source labels.
A minimum GEOMETRIC owner assignment need not preserve that provenance:
a foreign designated label can be contained in another standard.

For a vertex connector, full carrier containment is enough. By the
actual BigCycle's two incidence fields the vertex lies in the carriers
of both adjacent labels. For two distinct standards it is their common
core vertex, lying in both corresponding witness copies. For one
standard and a singleton core edge it lies in that local witness copy
and the true core edge. For two core edges it lies in both true core
edges. This verifies all four geometrically owned V-boundary cases
WITHOUT rewriting a foreign designated occurrence as an edge.

The wagon-boundary cases, construction of a cyclic segment word,
connector distinctness, legal reduct and A1--A3 remain separate.
No appendix input.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section GeometricSelectedCycleVertex

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
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- Physical standard/core vertex geometry without assuming that
the adjacent standard-owned label is a literal standard image. -/
theorem attachedSelectedPicture_geometric_standard_core_vertex
    (i : I) (b : CoreEdge) (x : Vertex)
    (hxStandard : x ∈ copyCarrier (Std i))
    (hxCoreEdge : x ∈ (CoreActual b).1) :
    ∃ y : Y,
      CoreEmb y = x ∧ y ∈ copyCarrier (f i) ∧ y ∈ b.1 := by
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

/-- Vertex boundary between DIFFERENT geometric standard owners:
both assigned labels can be foreign to the chosen standards.
The common vertex still has one witness-core preimage in Q_i ∩ Q_j. -/
theorem attachedSelectedPicture_geometric_vertex_two_standards
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (x : Vertex) (i j : I)
    (hij : i ≠ j)
    (hV : K.connector k = Sum.inl x)
    (hLeft : owner k = Sum.inl i)
    (hRight : owner (cyclicSucc k) = Sum.inl j) :
    ∃ y : Y, CoreEmb y = x ∧
      y ∈ copyCarrier (f i) ∧ y ∈ copyCarrier (f j) := by
  have hBoth :=
    OrderOneData.BigCycle.vertex_boundary_in_both_labels Out K k x hV
  have hxI : x ∈ copyCarrier (Std i) := by
    have hh := hAllowed k
    rw [hLeft] at hh
    exact hh hBoth.1
  have hxJ : x ∈ copyCarrier (Std j) := by
    have hh := hAllowed (cyclicSucc k)
    rw [hRight] at hh
    exact hh hBoth.2
  exact attachment_shared_point_in_both_local_images
    C.toRelStructure S R f hij hxI hxJ

/-- Vertex boundary from a geometric standard to a singleton core edge:
the actual core vertex belongs to that local witness copy and edge.
No original-source label for the standard occurrence is needed. -/
theorem attachedSelectedPicture_geometric_vertex_standard_core
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (x : Vertex) (i : I) (b : CoreEdge)
    (hV : K.connector k = Sum.inl x)
    (hLeft : owner k = Sum.inl i)
    (hRight : owner (cyclicSucc k) = Sum.inr b) :
    ∃ y : Y, CoreEmb y = x ∧
      y ∈ copyCarrier (f i) ∧ y ∈ b.1 := by
  have hBoth :=
    OrderOneData.BigCycle.vertex_boundary_in_both_labels Out K k x hV
  have hxStd : x ∈ copyCarrier (Std i) := by
    have hh := hAllowed k
    rw [hLeft] at hh
    exact hh hBoth.1
  have hCoreLabel : K.label (cyclicSucc k) =
      Sum.inr (CoreActual b) := by
    have hh := hAllowed (cyclicSucc k)
    rw [hRight] at hh
    exact hh
  have hxCore : x ∈ (CoreActual b).1 := by
    have hh := hBoth.2
    rw [hCoreLabel] at hh
    change x ∈ (CoreActual b).1 at hh
    exact hh
  exact attachedSelectedPicture_geometric_standard_core_vertex
    A hA D C e R f i b x hxStd hxCore

/-- Reverse orientation: singleton core edge followed by a geometric
standard owner. It has the same actual witness-core vertex. -/
theorem attachedSelectedPicture_geometric_vertex_core_standard
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (x : Vertex) (i : I) (b : CoreEdge)
    (hV : K.connector k = Sum.inl x)
    (hLeft : owner k = Sum.inr b)
    (hRight : owner (cyclicSucc k) = Sum.inl i) :
    ∃ y : Y, CoreEmb y = x ∧
      y ∈ copyCarrier (f i) ∧ y ∈ b.1 := by
  have hBoth :=
    OrderOneData.BigCycle.vertex_boundary_in_both_labels Out K k x hV
  have hxStd : x ∈ copyCarrier (Std i) := by
    have hh := hAllowed (cyclicSucc k)
    rw [hRight] at hh
    exact hh hBoth.2
  have hCoreLabel : K.label k = Sum.inr (CoreActual b) := by
    have hh := hAllowed k
    rw [hLeft] at hh
    exact hh
  have hxCore : x ∈ (CoreActual b).1 := by
    have hh := hBoth.1
    rw [hCoreLabel] at hh
    change x ∈ (CoreActual b).1 at hh
    exact hh
  exact attachedSelectedPicture_geometric_standard_core_vertex
    A hA D C e R f i b x hxStd hxCore

/-- Two geometric core-edge owners denote the corresponding literal
physical core edges. A vertex boundary has their common witness
vertex, with no train compatibility hypothesis. -/
theorem attachedSelectedPicture_geometric_vertex_core_core
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (x : Vertex) (b c : CoreEdge)
    (hV : K.connector k = Sum.inl x)
    (hLeft : owner k = Sum.inr b)
    (hRight : owner (cyclicSucc k) = Sum.inr c) :
    ∃ y : Y, CoreEmb y = x ∧ y ∈ b.1 ∧ y ∈ c.1 := by
  have hLabelB : K.label k = Sum.inr (CoreActual b) := by
    have hh := hAllowed k
    rw [hLeft] at hh
    exact hh
  have hLabelC : K.label (cyclicSucc k) =
      Sum.inr (CoreActual c) := by
    have hh := hAllowed (cyclicSucc k)
    rw [hRight] at hh
    exact hh
  exact attachedSelectedPicture_cycle_vertex_core_core_local
    A hA B D C family selected e R f T U hShared μ
    K k x b c hV hLabelB hLabelC

end GeometricSelectedCycleVertex
end StructuralRamsey.Girth

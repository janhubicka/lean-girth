import Girth.TrainFillingIndexedEdgeFlatten
import Girth.TrainFillingSelectedEdgeRange

set_option Elab.async false

/-!
# The actual heterogeneous G0 physical edge map into the full filling H

The verified indexed-choice flattening represents every physical edge
of G0 by (contracted first wagon, local X-template edge), without
identifying any different occurrence labels. The verified uniform
filling edge equivalence sends those pairs bijectively onto actual
physical edges of the complete filled H.

Given the physical old-edge embedding of the selected contracted M,
we therefore CONSTRUCT the entire heterogeneous G0-to-H physical
edge embedding, its exact old cover, and its complete range.
No independently assumed output edge map or pruning of H edges.

If the selected vertex embedding identifies each entire canonical X
placement pointwise, exact edge carrier transport also follows for
EVERY heterogeneous local edge, including edges outside the chosen
W* subfamily. This is still conditional on the actual selected
ordered M-copy and its whole-first-wagon placement compatibility.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Y : Type v}
variable (U : C → PrivateWagonInput V P X)
variable (H : UniformFillingData Y X)
variable (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)

/-- Every indexed G0 physical edge gets its actual new filled H edge.
No additional output edge injection is supplied as an input. -/
noncomputable def selectedIndexedFilledEdgeEmbedding
    (β : (C × P) ↪ H.OldEdge) :
    Edge U ↪ H.toTrainFilling.NewEdge where
  toFun := fun a => H.selectedFilledEdgeEmbedding β
    (edgeIndexEquiv U H.templateEdges hTemplate a)
  inj' := by
    intro a b hab
    have hFlat :
        edgeIndexEquiv U H.templateEdges hTemplate a =
          edgeIndexEquiv U H.templateEdges hTemplate b :=
      (H.selectedFilledEdgeEmbedding β).injective hab
    exact (edgeIndexEquiv U H.templateEdges hTemplate).injective hFlat

/-- The actual old physical cover of the filled G0 edge is its
selected contracted first wagon, including the choice tag. -/
@[simp] theorem selectedIndexedFilledEdgeEmbedding_cover
    (β : (C × P) ↪ H.OldEdge) (a : Edge U) :
    H.toTrainFilling.cover
      (selectedIndexedFilledEdgeEmbedding U H hTemplate β a) =
        β (a.1, a.2.1) := by
  change H.toTrainFilling.cover
    (H.selectedFilledEdgeEmbedding β
      (edgeIndexEquiv U H.templateEdges hTemplate a)) =
        β (a.1, a.2.1)
  simpa only [H.selectedFilledEdgeEmbedding_cover,
    edgeIndexEquiv_old]

/-- The FULL image of the indexed heterogeneous edge map is exactly
the ambient H-edge family over the selected old first wagons. Neither
unused ambient old edges nor their filled edges are deleted. -/
theorem selectedIndexedFilledEdgeEmbedding_range
    (β : (C × P) ↪ H.OldEdge) :
    Set.range (selectedIndexedFilledEdgeEmbedding U H hTemplate β) =
      {e : H.toTrainFilling.NewEdge |
        H.toTrainFilling.cover e ∈ Set.range β} := by
  calc
    Set.range (selectedIndexedFilledEdgeEmbedding U H hTemplate β) =
        Set.range (H.selectedFilledEdgeEmbedding β) := by
      ext e
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨edgeIndexEquiv U H.templateEdges hTemplate a, ha⟩
      · rintro ⟨t, ht⟩
        obtain ⟨a, ha⟩ :=
          (edgeIndexEquiv U H.templateEdges hTemplate).surjective t
        refine ⟨a, ?_⟩
        change H.selectedFilledEdgeEmbedding β
          (edgeIndexEquiv U H.templateEdges hTemplate a) = e
        rw [ha]
        exact ht
    _ = {e : H.toTrainFilling.NewEdge |
          H.toTrainFilling.cover e ∈ Set.range β} :=
      H.selectedFilledEdgeEmbedding_range β

/-- A single pointwise compatibility identity with canonical X
placements gives literal vertex-carrier transport for every full
heterogeneous G0 physical edge. -/
theorem selectedIndexedFilledEdgeEmbedding_carrier
    (β : (C × P) ↪ H.OldEdge)
    (vertex : Vertex U ↪ Y)
    (hPlace : ∀ c : C, ∀ p : P, ∀ x : X,
      H.place (β (c, p)) x =
        vertex (tagVertex U c ((U c).place p x)))
    (a : Edge U) :
    (selectedIndexedFilledEdgeEmbedding U H hTemplate β a).1 =
      vertex '' edgeCarrier U a := by
  change H.place (β (a.1, a.2.1)) '' a.2.2.1 =
    vertex '' (tagVertex U a.1 '' ((U a.1).place a.2.1 '' a.2.2.1))
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨tagVertex U a.1 ((U a.1).place a.2.1 x), ?_, ?_⟩
    · exact ⟨(U a.1).place a.2.1 x, ⟨x, hx, rfl⟩, rfl⟩
    · exact (hPlace a.1 a.2.1 x).symm
  · rintro ⟨w, ⟨z, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨x, hx, (hPlace a.1 a.2.1 x).symm⟩

end StructuralRamsey.Girth.IndexedPrivateChoice

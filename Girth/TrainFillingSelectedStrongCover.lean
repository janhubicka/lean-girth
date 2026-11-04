import Girth.TrainFillingTemplateConstruction

set_option Elab.async false

/-!
# Strong old selected copies own exactly their contained filled edges

A physical filled edge e is contained in its unique old cover F.cover e.
For a strongly induced selected old M-copy B, the converse direction
uses two distinct vertices of EVERY local template edge: if e lies in
the selected vertex carrier, its old cover meets that carrier in two
vertices, hence the old strongness forces the old cover into B.

Therefore the complete ambient filled-edge set contained in a selected
copy is exactly the cover-pullback of that selected old edge set. This
is NOT a restriction of the ambient hypergraph and NO output selected
edge coverage is taken as an input.

The actual shorter-train witness still has to supply the selected old
M-copy and its genuine strongness/edge containment. This file does not
assert the final Ramsey arrow, parentwise realization or top-cut girth.
-/

namespace StructuralRamsey.Girth.UniformFillingData

universe v
variable {V X : Type v} (U : UniformFillingData V X)

/-- The generated physical-edge type inherits a literal two-vertex
condition from the template. This is stronger than mere nonemptiness,
and is precisely what makes the converse selected-cover implication
possible. -/
theorem generatedEdge_has_distinct_pair
    (e : U.toTrainFilling.NewEdge) :
    ∃ x y : V, x ≠ y ∧ x ∈ e.1 ∧ y ∈ e.1 := by
  obtain ⟨x, y, hxy, hx, hy⟩ := U.template_pair (U.decode e).2
  let f := (U.decode e).1
  have hxE : U.place f x ∈ e.1 := by
    rw [← U.imageCarrier_decode e]
    exact ⟨x, hx, rfl⟩
  have hyE : U.place f y ∈ e.1 := by
    rw [← U.imageCarrier_decode e]
    exact ⟨y, hy, rfl⟩
  have hDistinct : U.place f x ≠ U.place f y := by
    intro h
    exact hxy ((U.place f).injective h)
  exact ⟨U.place f x, U.place f y, hDistinct, hxE, hyE⟩

/-- A selected old M-copy is strong when any old physical edge that
meets its vertex carrier in two distinct vertices belongs to its old
edge family. Under that precise old strongness hypothesis, containment
of an ACTUAL new filled edge in the selected carrier is equivalent to
membership of its ACTUAL old cover in the selected old edge family. -/
theorem generatedEdge_subset_iff_cover_mem
    (carrier : Set V)
    (selectedOldEdges : Set U.OldEdge)
    (hSelectedContained : ∀ f : U.OldEdge,
      f ∈ selectedOldEdges → f.1 ⊆ carrier)
    (hOldStrong : ∀ f : U.OldEdge,
      ¬ (f.1 ∩ carrier).Subsingleton → f ∈ selectedOldEdges)
    (e : U.toTrainFilling.NewEdge) :
    e.1 ⊆ carrier ↔
      U.toTrainFilling.cover e ∈ selectedOldEdges := by
  constructor
  · intro hContained
    obtain ⟨x, y, hne, hx, hy⟩ := U.generatedEdge_has_distinct_pair e
    have hNotSub :
        ((U.toTrainFilling.cover e).1 ∩ carrier).Subsingleton → False := by
      intro hSub
      exact hne (hSub
        ⟨U.toTrainFilling.contained e hx, hContained hx⟩
        ⟨U.toTrainFilling.contained e hy, hContained hy⟩)
    exact hOldStrong (U.toTrainFilling.cover e) hNotSub
  · intro he z hz
    exact hSelectedContained (U.toTrainFilling.cover e) he
      (U.toTrainFilling.contained e hz)

/-- Equality of the COMPLETE sets of physical filled edges. The ambient
edge type and all its wagons are left unchanged; only a copy-edge SET is
identified by this theorem. -/
theorem generatedEdges_selected_exact
    (carrier : Set V)
    (selectedOldEdges : Set U.OldEdge)
    (hSelectedContained : ∀ f : U.OldEdge,
      f ∈ selectedOldEdges → f.1 ⊆ carrier)
    (hOldStrong : ∀ f : U.OldEdge,
      ¬ (f.1 ∩ carrier).Subsingleton → f ∈ selectedOldEdges) :
    {e : U.toTrainFilling.NewEdge | e.1 ⊆ carrier} =
      {e | U.toTrainFilling.cover e ∈ selectedOldEdges} := by
  ext e
  exact U.generatedEdge_subset_iff_cover_mem
    carrier selectedOldEdges hSelectedContained hOldStrong e

end StructuralRamsey.Girth.UniformFillingData

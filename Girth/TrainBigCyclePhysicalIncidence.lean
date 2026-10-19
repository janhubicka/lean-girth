import Girth.TrainBigCycleOrderOneExtraction

/-!
# Circulation: source edges at the two sides of every cyclic boundary

The literal BigCycle definition already contains physical incidence at
each connector, on BOTH adjacent labels. We unpack those witnesses so
the segmented witness-reduction construction can transport them to
standard or witness-core edges without assuming a new incidence axiom.

No segmentation or reduct is postulated. No appendix imports.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A wagon connector of an actual big cycle provides a genuine
source edge from each adjacent label, both in the same old wagon. -/
theorem BigCycle.wagon_boundary_incidence_edges
    {n : ℕ} (C : D.BigCycle n) (i : Fin n) (p : P)
    (hW : C.connector i = Sum.inr p) :
    ∃ e f : E,
      e ∈ D.edges (C.label i) ∧ D.parent e = p ∧
      f ∈ D.edges (C.label (cyclicSucc i)) ∧ D.parent f = p := by
  have hLeft := C.left_incident i
  have hRight := C.right_incident i
  rw [hW] at hLeft hRight
  change D.Meets (C.label i) p at hLeft
  change D.Meets (C.label (cyclicSucc i)) p at hRight
  rcases hLeft with ⟨e, he, hep⟩
  rcases hRight with ⟨f, hf, hfp⟩
  exact ⟨e, f, he, hep, hf, hfp⟩

/-- A vertex boundary is a genuine vertex in each adjacent label,
rather than merely a point of the ambient output picture. -/
theorem BigCycle.vertex_boundary_in_both_labels
    {n : ℕ} (C : D.BigCycle n) (i : Fin n) (x : V)
    (hV : C.connector i = Sum.inl x) :
    x ∈ D.carrier (C.label i) ∧
      x ∈ D.carrier (C.label (cyclicSucc i)) := by
  have hLeft := C.left_incident i
  have hRight := C.right_incident i
  rw [hV] at hLeft hRight
  change x ∈ D.carrier (C.label i) at hLeft
  change x ∈ D.carrier (C.label (cyclicSucc i)) at hRight
  exact ⟨hLeft, hRight⟩

end StructuralRamsey.Girth.OrderOneData

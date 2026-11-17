import Girth.ForestToSupremeBottom

/-!
# Bottom wagon incidence puts the shared physical edge in its neighbour

At the equality cut, the parent map from edges to wagon labels is injective.
Consequently, any label meeting the wagon of e physically contains e.
These two facts are the geometry used when swapping an isolated edge
occurrence to the picture owner on its wagon side.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- An edge label meets precisely its own bottom wagon (in fact at any cut). -/
theorem parent_eq_of_edge_label_wagon_incidence
    (e : E) (p : P) (h : D.Incident (.inr e) (.inr p)) :
    D.parent e = p := by
  obtain ⟨f, hf, hp⟩ := h
  have hfe : f = e := hf
  subst f
  exact hp

/-- Under bottom parent injectivity, meeting the wagon of e forces
physical containment of e, not merely a shared vertex. -/
theorem BottomForestGeometry.edgeCarrier_subset_of_wagon_meet
    (H : D.BottomForestGeometry) (a : I ⊕ E) (e : E)
    (hMeet : D.Meets a (D.parent e)) :
    D.edgeCarrier e ⊆ D.carrier a := by
  obtain ⟨f, hf, hParent⟩ := hMeet
  have hEq : f = e := H.parent_injective hParent
  subst f
  exact H.edge_subset a e hf

/-- The next label at a wagon connector contains the entire physical
edge named by the bottom wagon. -/
theorem BigCycle.next_carrier_contains_bottom_wagon_edge
    {n : ℕ} (C : D.BigCycle n) (H : D.BottomForestGeometry)
    (k : Fin n) (e : E)
    (hWagon : C.connector k = .inr (D.parent e)) :
    D.edgeCarrier e ⊆ D.carrier (C.label (cyclicSucc k)) := by
  have hMeet : D.Meets (C.label (cyclicSucc k)) (D.parent e) := by
    have h := C.right_incident k
    rw [hWagon] at h
    exact h
  exact H.edgeCarrier_subset_of_wagon_meet D _ e hMeet

/-- The previous label at a wagon connector contains the entire physical
edge named by the bottom wagon. -/
theorem BigCycle.previous_carrier_contains_bottom_wagon_edge
    {n : ℕ} (C : D.BigCycle n) (H : D.BottomForestGeometry)
    (k : Fin n) (e : E)
    (hWagon : C.connector (trainCyclicPred k) = .inr (D.parent e)) :
    D.edgeCarrier e ⊆ D.carrier (C.label (trainCyclicPred k)) := by
  have hMeet : D.Meets (C.label (trainCyclicPred k)) (D.parent e) := by
    have h := C.left_incident (trainCyclicPred k)
    rw [hWagon] at h
    exact h
  exact H.edgeCarrier_subset_of_wagon_meet D _ e hMeet

end StructuralRamsey.Girth.OrderOneData

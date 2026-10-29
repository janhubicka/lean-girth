import Girth.ForestToSupremeBottom
import Girth.ForestEnumeration

/-!
# Switching across a leaf of the bottom support forest

Occurrences may be assigned to a forest member containing their physical
carrier and edges.  This deliberately permits a short edge replacement to
be reassigned from a deleted leaf to its parent.  No deletion of arbitrary
designated members is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P K : Type v} (D : OrderOneData V E I P)

/-- All incidences with one actual edge occur in two consecutive positions.
The wagon-connector case uses A2, including its no-common-edge clause through
the previously checked three-incidence obstruction; the other case uses A3. -/
theorem BigCycle.edge_incident_positions_consecutive
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable) (e : E) :
    ∃ i : Fin n, ∀ j : Fin n, D.Incident (.inr e) (C.connector j) →
      j = i ∨ j = cyclicSucc i := by
  classical
  have hClass (j : Fin n) (hj : D.Incident (.inr e) (C.connector j)) :
      C.InWagonAt (D.parent e) j ∨ C.connector j = .inr (D.parent e) := by
    cases hq : C.connector j with
    | inl x =>
        exact Or.inl ⟨x, hq, e, rfl, by simpa [hq, Incident, carrier] using hj⟩
    | inr p =>
        have hm : D.Meets (.inr e) p := by simpa [hq, Incident] using hj
        obtain ⟨f, hf, hfp⟩ := hm
        have hfe : f = e := hf
        subst f
        exact Or.inr (congrArg Sum.inr hfp.symm)
  by_cases hw : ∃ w : Fin n, C.connector w = .inr (D.parent e)
  · obtain ⟨w, hw⟩ := hw
    have hew : D.Incident (.inr e) (C.connector w) := by
      rw [hw]
      exact ⟨e, rfl, rfl⟩
    by_cases hx : ∃ x : Fin n, x ≠ w ∧ D.Incident (.inr e) (C.connector x)
    · obtain ⟨x, hxw, hex⟩ := hx
      have hxNeighbor : x = trainCyclicPred w ∨ x = cyclicSucc w := by
        rcases hClass x hex with hx | hx
        · exact hAccept.2.1.1 w (D.parent e) hw x hx
        · exact (hxw (C.connector_injective (hx.trans hw.symm))).elim
      have hOnly (j : Fin n) (hj : D.Incident (.inr e) (C.connector j)) :
          j = w ∨ j = x := by
        by_contra h
        push Not at h
        exact C.not_edge_incident_three_distinct D hAccept e w x j
          hxw.symm h.1.symm h.2.symm hew hex hj
      rcases hxNeighbor with hx | hx
      · refine ⟨x, ?_⟩
        intro j hj
        rcases hOnly j hj with hjw | hjx
        · right
          rw [hx, cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two, hjw]
        · exact Or.inl hjx
      · refine ⟨w, ?_⟩
        intro j hj
        exact (hOnly j hj).imp_right (fun hjx => hjx.trans hx)
    · refine ⟨w, ?_⟩
      intro j hj
      left
      by_contra hjw
      exact hx ⟨j, hjw, hj⟩
  · obtain ⟨i, hi⟩ := hAccept.2.2 (D.parent e) (by
      intro j hj
      exact hw ⟨j, hj⟩)
    refine ⟨i, ?_⟩
    intro j hj
    rcases hClass j hj with hv | hwj
    · exact hi j hv
    · exact (hw ⟨j, hwj⟩).elim

/-- Incidence is preserved when one label is carried by a forest member. -/
theorem incident_of_carrier_edges_subset
    {a b : I ⊕ E}
    (hc : D.carrier a ⊆ D.carrier b)
    (he : D.edges a ⊆ D.edges b)
    {q : V ⊕ P} (hq : D.Incident a q) : D.Incident b q := by
  cases q with
  | inl x => exact hc hq
  | inr p =>
      obtain ⟨e, hea, hep⟩ := hq
      exact ⟨e, he hea, hep⟩

/-- Running intersections transport a shared bottom wagon edge from a leaf
and another member to the leaf's parent. -/
theorem BottomForestGeometry.leaf_shared_edge_mem_parent
    (H : D.BottomForestGeometry) (member : K → I ⊕ E)
    (J : JoinTree (fun k => D.bottomForestPiece H (member k)))
    {leaf parent other : K}
    (hAdj : J.tree.Adj leaf parent)
    (hUnique : ∀ k : K, J.tree.Adj leaf k → k = parent)
    (hOther : other ≠ leaf)
    {e : E} (hel : e ∈ D.edges (member leaf))
    (heo : e ∈ D.edges (member other)) :
    D.edgeCarrier e ⊆ D.carrier (member parent) := by
  intro x hx
  exact J.mem_parent_of_mem_leaf_and_other hAdj hUnique hOther
    (H.edge_subset (member leaf) e hel hx)
    (H.edge_subset (member other) e heo hx)

/-- Every connector crossing between a leaf and the other forest members
lies on their physical separator edge. -/
theorem BottomForestGeometry.leaf_switch_incident
    (H : D.BottomForestGeometry) (member : K → I ⊕ E)
    (J : JoinTree (fun k => D.bottomForestPiece H (member k)))
    {leaf parent other : K}
    (hAdj : J.tree.Adj leaf parent)
    (hUnique : ∀ k : K, J.tree.Adj leaf k → k = parent)
    (hOther : other ≠ leaf)
    {e : E}
    (hInter : D.carrier (member leaf) ∩ D.carrier (member parent) =
      D.edgeCarrier e)
    {q : V ⊕ P}
    (hLeaf : D.Incident (member leaf) q)
    (hOtherInc : D.Incident (member other) q) :
    D.Incident (.inr e) q := by
  cases q with
  | inl x =>
      change x ∈ D.edgeCarrier e
      rw [← hInter]
      exact ⟨hLeaf,
        J.mem_parent_of_mem_leaf_and_other hAdj hUnique hOther hLeaf hOtherInc⟩
  | inr p =>
      obtain ⟨f, hfl, hfo, hfp⟩ := H.common_edge_of_meets D hLeaf hOtherInc
      have hfe : f = e := H.edge_eq_of_subset D (by
        intro x hx
        rw [← hInter]
        exact ⟨H.edge_subset (member leaf) f hfl hx,
          H.leaf_shared_edge_mem_parent D member J hAdj hUnique hOther hfl hfo hx⟩)
      exact ⟨e, rfl, by simpa [hfe] using hfp⟩

end StructuralRamsey.Girth.OrderOneData

import Girth.TrainRecursiveInitialTailGirth

/-!
# The source-order budget for used parent wagons

Every vertex connector contributes two units to the sum of the two adjacent
lower bounds on occurrence weights.  Thus twice the number of vertex
connectors is at most the actual source twice-order, without any restriction
on adjacent connector kinds.

For a nonconstant edge-parent word, every used parent has an outgoing change.
The actual connector at such a change must be a vertex.  Sending each vertex
position to its left parent is therefore onto the used parent labels.  These
two facts derive the required finite-label budget directly from source order.
-/

namespace StructuralRamsey.Girth

universe v

namespace OrderOneData.BigCycle

variable {V E I P : Type v} {D : OrderOneData V E I P}
variable {n : ℕ} (C : D.BigCycle n)

/-- Vertex-connector positions are counted in the literal source word. -/
abbrev VertexPosition := {i : Fin n // ∃ x : V, C.connector i = Sum.inl x}

/-- Twice the actual number of vertex connectors is at most source order.
The inequality is valid for every big cycle, including adjacent wagons. -/
theorem two_vertexPosition_card_le_twiceOrder :
    2 * Nat.card C.VertexPosition ≤ C.twiceOrder := by
  classical
  let indicator : Fin n → ℕ := fun i =>
    if ∃ x : V, C.connector i = Sum.inl x then 1 else 0
  have hCount : Nat.card C.VertexPosition = ∑ i : Fin n, indicator i := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {i : Fin n // ∃ x : V, C.connector i = Sum.inl x} = _
    rw [Fintype.card_subtype, Finset.card_filter]
  have hRotate : (∑ i : Fin n, indicator (cyclicSucc i)) =
      ∑ i : Fin n, indicator i := by
    simpa only [cyclicSucc_eq_finRotate] using Equiv.sum_comp (finRotate n) indicator
  calc
    2 * Nat.card C.VertexPosition =
        (∑ i : Fin n, indicator i) + ∑ i : Fin n, indicator (cyclicSucc i) := by
      rw [hCount, hRotate]
      omega
    _ = ∑ i : Fin n, (indicator i + indicator (cyclicSucc i)) :=
      Finset.sum_add_distrib.symm
    _ ≤ C.twiceOrder := by
      apply Finset.sum_le_sum
      intro i _
      cases hLeft : C.connector i <;> cases hRight : C.connector (cyclicSucc i) <;>
        simp [indicator, hLeft, hRight, connectorKind, twiceOccurrenceWeight]

/-- The source twice-order cutoff bounds the number of vertex positions. -/
theorem vertexPosition_card_le_of_twiceOrder_le
    (q : ℕ) (hOrder : C.twiceOrder ≤ 2 * q) :
    Nat.card C.VertexPosition ≤ q := by
  have h := C.two_vertexPosition_card_le_twiceOrder
  omega

include C

/-- Every used value of a nonconstant cyclic word occurs just before an
outgoing change.  The proof retains the actual cyclic index. -/
theorem used_owner_has_outgoing_change
    {Owner : Type v} (owner : Fin n → Owner)
    (hNonconstant : ∃ i j, owner i ≠ owner j)
    (p : Owner) (hp : p ∈ Set.range owner) :
    ∃ k : Fin n, owner k = p ∧ owner (cyclicSucc k) ≠ p := by
  classical
  obtain ⟨i, hi⟩ := hp
  have hOther : ∃ j, owner j ≠ p := by
    obtain ⟨a, b, hab⟩ := hNonconstant
    by_cases ha : owner a = p
    · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
    · exact ⟨a, ha⟩
  obtain ⟨j, hj⟩ := hOther
  let side : Fin n → Bool := fun k => decide (owner k = p)
  have hMixed : ∃ a b, side a ≠ side b := by
    refine ⟨i, j, ?_⟩
    simp [side, hi, hj]
  obtain ⟨k, off, _, hk, hnext, _, _, _⟩ :=
    exists_false_cyclic_run C.length_ge_two side hMixed
  exact ⟨k, of_decide_eq_true hk, of_decide_eq_false hnext⟩

/-- For an edge-only cycle with a nonconstant parent word, the literal
vertex positions cover all used parent labels. -/
theorem used_parent_card_le_vertexPosition_card
    (edge : Fin n → E) (hLabel : ∀ i, C.label i = Sum.inr (edge i))
    (hNonconstant : ∃ i j, D.parent (edge i) ≠ D.parent (edge j)) :
    Nat.card (Set.range (fun i => D.parent (edge i))) ≤
      Nat.card C.VertexPosition := by
  classical
  let owner : Fin n → P := fun i => D.parent (edge i)
  let Used : Type v := Set.range owner
  let allPicked : Fin n → Used := fun k => ⟨owner k, ⟨k, rfl⟩⟩
  have hAllOnto : Function.Surjective allPicked := by
    rintro ⟨p, ⟨k, hk⟩⟩
    exact ⟨k, Subtype.ext hk⟩
  haveI : Finite Used := Finite.of_surjective allPicked hAllOnto
  letI : Fintype Used := Fintype.ofFinite Used
  let picked : C.VertexPosition → Used := fun k => allPicked k.val
  have hOnto : Function.Surjective picked := by
    intro p
    obtain ⟨k, hk, hnext⟩ := C.used_owner_has_outgoing_change owner hNonconstant p.val p.property
    have hVertex : ∃ x : V, C.connector k = Sum.inl x := by
      cases hConnector : C.connector k with
      | inl x => exact ⟨x, rfl⟩
      | inr wagon =>
          have hLeft := C.left_incident k
          have hRight := C.right_incident k
          rw [hLabel k, hConnector] at hLeft
          rw [hLabel (cyclicSucc k), hConnector] at hRight
          obtain ⟨e, he, hep⟩ := hLeft
          obtain ⟨f, hf, hfp⟩ := hRight
          have heq : e = edge k := he
          have hfq : f = edge (cyclicSucc k) := hf
          subst e
          subst f
          exact (hnext ((hfp.trans hep.symm).trans hk)).elim
    exact ⟨⟨k, hVertex⟩, Subtype.ext hk⟩
  have h := Fintype.card_le_of_surjective picked hOnto
  simpa only [Nat.card_eq_fintype_card] using h

/-- The finite used-label budget is derived from source order, not assumed
as an independent cycle bound. -/
theorem used_parent_card_le_of_twiceOrder_le
    (edge : Fin n → E) (hLabel : ∀ i, C.label i = Sum.inr (edge i))
    (hNonconstant : ∃ i j, D.parent (edge i) ≠ D.parent (edge j))
    (q : ℕ) (hOrder : C.twiceOrder ≤ 2 * q) :
    Nat.card (Set.range (fun i => D.parent (edge i))) ≤ q :=
  (C.used_parent_card_le_vertexPosition_card edge hLabel hNonconstant).trans
    (C.vertexPosition_card_le_of_twiceOrder_le q hOrder)

end OrderOneData.BigCycle
end StructuralRamsey.Girth

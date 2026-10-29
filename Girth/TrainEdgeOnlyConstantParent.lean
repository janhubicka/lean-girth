import Girth.TrainBigCycleOrderOneExtraction

/-!
# An acceptable edge-only cycle cannot have one constant parent

Every wagon connector of an edge-only cycle is the parent of both adjacent
edges.  If all parents agree, injectivity permits at most one wagon connector
and every vertex connector belongs to that same wagon.  A3 then restricts a
cycle without wagon connectors to length two; physical edge linearity rules
it out.  If the wagon occurs, A2 restricts the cycle to length at most three.
The two-occurrence case contradicts A1, while the three-occurrence case
contradicts A2's actual ambient-edge prohibition.

No labelled cut-girth or supreme-cycle hypothesis is used here.  This is the
constant-parent half of the edge-only obstruction, with the literal A1--A3
conditions and only physical edge linearity.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} {D : OrderOneData V E I P}

private theorem card_le_two_of_pair_cover {J : Type*} [Fintype J]
    (a b : J) (h : ∀ j : J, j = a ∨ j = b) : Fintype.card J ≤ 2 := by
  classical
  have hs : (Finset.univ : Finset J) ⊆ {a, b} := by
    intro j hj
    rcases h j with rfl | rfl <;> simp
  exact (Finset.card_le_card hs).trans (Finset.card_le_two (a := a) (b := b))

private theorem card_le_three_of_triple_cover {J : Type*} [Fintype J]
    (a b c : J) (h : ∀ j : J, j = a ∨ j = b ∨ j = c) :
    Fintype.card J ≤ 3 := by
  classical
  have hs : (Finset.univ : Finset J) ⊆ {a, b, c} := by
    intro j hj
    rcases h j with rfl | rfl | rfl <;> simp
  calc
    Fintype.card J ≤ ({a, b, c} : Finset J).card := Finset.card_le_card hs
    _ ≤ ({b, c} : Finset J).card + 1 := Finset.card_insert_le _ _
    _ ≤ 2 + 1 := Nat.add_le_add_right (Finset.card_le_two (a := b) (b := c)) 1

/-- Under physical edge linearity, an acceptable edge-only cycle cannot
have a constant parent label.  Labels may repeat at nonadjacent positions;
only the genuine adjacent-label inequalities of the cycle are used.
-/
theorem BigCycle.false_of_edge_only_constant_parent
    {n : ℕ} (C : D.BigCycle n)
    (edge : Fin n → E) (hLabel : ∀ i, C.label i = Sum.inr (edge i))
    (p : P) (hParent : ∀ i, D.parent (edge i) = p)
    (hEdgeLinear : ∀ e f : E, e ≠ f →
      (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (hAccept : C.Acceptable) : False := by
  classical
  have hLeft : ∀ (i : Fin n) (x : V), C.connector i = Sum.inl x →
      x ∈ D.edgeCarrier (edge i) := by
    intro i x hx
    have hi := C.left_incident i
    rw [hLabel i, hx] at hi
    exact hi
  have hRight : ∀ (i : Fin n) (x : V), C.connector i = Sum.inl x →
      x ∈ D.edgeCarrier (edge (cyclicSucc i)) := by
    intro i x hx
    have hi := C.right_incident i
    rw [hLabel (cyclicSucc i), hx] at hi
    exact hi
  have hWagon : ∀ (i : Fin n) (w : P), C.connector i = Sum.inr w → w = p := by
    intro i w hw
    have hi := C.left_incident i
    rw [hLabel i, hw] at hi
    obtain ⟨f, hf, hfp⟩ := hi
    have hfe : f = edge i := hf
    subst f
    exact hfp.symm.trans (hParent i)
  have hVertex : ∀ (i : Fin n) (x : V), C.connector i = Sum.inl x →
      D.WagonVertex p x := by
    intro i x hx
    exact ⟨edge i, hParent i, hLeft i x hx⟩
  by_cases hW : ∃ k : Fin n, C.connector k = Sum.inr p
  · obtain ⟨k, hk⟩ := hW
    have hOtherVertex : ∀ j : Fin n, j ≠ k →
        ∃ x : V, C.connector j = Sum.inl x ∧ D.WagonVertex p x := by
      intro j hj
      cases hc : C.connector j with
      | inl x => exact ⟨x, rfl, hVertex j x hc⟩
      | inr w =>
          have hwp := hWagon j w hc
          have hjk : j = k := C.connector_injective
            (hc.trans ((congrArg Sum.inr hwp).trans hk.symm))
          exact (hj hjk).elim
    have hCover : ∀ j : Fin n,
        j = k ∨ j = trainCyclicPred k ∨ j = cyclicSucc k := by
      intro j
      by_cases hj : j = k
      · exact Or.inl hj
      · obtain ⟨x, hx, hxp⟩ := hOtherVertex j hj
        exact Or.inr (hAccept.2.1.1 k p hk j ⟨x, hx, hxp⟩)
    have hnle : n ≤ 3 := by
      simpa only [Fintype.card_fin] using
        card_le_three_of_triple_cover k (trainCyclicPred k) (cyclicSucc k) hCover
    have hn : n = 2 ∨ n = 3 := by have := C.length_ge_two; omega
    rcases hn with rfl | rfl
    · have hOrder : C.twiceOrder = 2 := by
        fin_cases k
        · change C.connector 0 = Sum.inr p at hk
          obtain ⟨x, hx, _⟩ := hOtherVertex 1 (by decide)
          simp [BigCycle.twiceOrder, Fin.sum_univ_two, cyclicSucc,
            hk, hx, connectorKind, twiceOccurrenceWeight]
        · change C.connector 1 = Sum.inr p at hk
          obtain ⟨x, hx, _⟩ := hOtherVertex 0 (by decide)
          simp [BigCycle.twiceOrder, Fin.sum_univ_two, cyclicSucc,
            hk, hx, connectorKind, twiceOccurrenceWeight]
      obtain ⟨j, hj⟩ := hAccept.1 hOrder
      rw [hLabel j] at hj
      exact hj
    · have hPrev : trainCyclicPred k ≠ k := by fin_cases k <;> decide
      have hNext : cyclicSucc k ≠ k := by fin_cases k <;> decide
      have hDistinct : trainCyclicPred k ≠ cyclicSucc k := by fin_cases k <;> decide
      have hSuccSucc : cyclicSucc (cyclicSucc k) = trainCyclicPred k := by
        fin_cases k <;> rfl
      obtain ⟨x, hx, hxp⟩ := hOtherVertex (trainCyclicPred k) hPrev
      obtain ⟨y, hy, hyp⟩ := hOtherVertex (cyclicSucc k) hNext
      have hxy : D.PairEdge x y := by
        refine ⟨edge (trainCyclicPred k), hLeft _ x hx, ?_⟩
        rw [← hSuccSucc]
        exact hRight (cyclicSucc k) y hy
      exact (hAccept.2.1.2 k p x y hk hx hy hDistinct hxp hyp) hxy
  · have hNoWagon : ∀ i : Fin n, C.connector i ≠ Sum.inr p := by
      intro i hi
      exact hW ⟨i, hi⟩
    have hAllVertex : ∀ i : Fin n, ∃ x : V, C.connector i = Sum.inl x := by
      intro i
      cases hi : C.connector i with
      | inl x => exact ⟨x, rfl⟩
      | inr w =>
          have hwp := hWagon i w hi
          exact (hNoWagon i (hi.trans (congrArg Sum.inr hwp))).elim
    obtain ⟨k, hk⟩ := hAccept.2.2 p hNoWagon
    have hCover : ∀ j : Fin n, j = k ∨ j = cyclicSucc k := by
      intro j
      obtain ⟨x, hx⟩ := hAllVertex j
      exact hk j ⟨x, hx, hVertex j x hx⟩
    have hnle : n ≤ 2 := by
      simpa only [Fintype.card_fin] using card_le_two_of_pair_cover k (cyclicSucc k) hCover
    have hn : n = 2 := by have := C.length_ge_two; omega
    subst n
    obtain ⟨x, hx⟩ := hAllVertex 0
    obtain ⟨y, hy⟩ := hAllVertex 1
    have hEdgeNe : edge 0 ≠ edge 1 := by
      intro h
      apply C.adjacent_ne 0
      simpa [hLabel, cyclicSucc] using congrArg (Sum.inr : E → I ⊕ E) h
    have hxBoth : x ∈ D.edgeCarrier (edge 0) ∩ D.edgeCarrier (edge 1) := by
      exact ⟨hLeft 0 x hx, by simpa [cyclicSucc] using hRight 0 x hx⟩
    have hyBoth : y ∈ D.edgeCarrier (edge 0) ∩ D.edgeCarrier (edge 1) := by
      exact ⟨by simpa [cyclicSucc] using hRight 1 y hy, hLeft 1 y hy⟩
    have hxy : x = y := hEdgeLinear (edge 0) (edge 1) hEdgeNe hxBoth hyBoth
    have h01 : (0 : Fin 2) = 1 := C.connector_injective
      (hx.trans ((congrArg Sum.inl hxy).trans hy.symm))
    exact (by decide : (0 : Fin 2) ≠ 1) h01

end StructuralRamsey.Girth.OrderOneData

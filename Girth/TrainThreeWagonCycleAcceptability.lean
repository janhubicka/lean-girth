import Girth.TrainOutputA1Length
import Mathlib.Tactic

/-!
# Circulation: three-occurrence cycles with one wagon connector

A source cycle of length two can replace its one non-kept occurrence
by a long piece. Its literal result has three occurrences, TWO
original vertex connectors, and exactly one fresh wagon between them.

The A2 and A3 conditions of that result are elementary:
* A2: the only wagon connector sees only the other two, consecutive,
  vertex positions; its no-common-edge clause follows from LongValid.
* A3: another wagon sees at most two vertex positions, and every pair
  of positions among the two vertices is consecutive in this 3-cycle.
* A1: length three rules out order one automatically.

This file certifies those concrete two orientations independently of
any general source-to-output A2/A3 transportation theorem. It does
not assume output-wagon linearity, general admissible replacement,
or the appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- On a 3-cycle with connector shape (vertex x, wagon w, vertex y),
the no-common-edge condition on x,y suffices for A2 and A3. -/
theorem BigCycle.three_vwv_acceptable
    (B : D.BigCycle 3) (x y : V) (w : P)
    (h0 : B.connector 0 = Sum.inl x)
    (h1 : B.connector 1 = Sum.inr w)
    (h2 : B.connector 2 = Sum.inl y)
    (hNoPair : ¬ D.PairEdge x y) :
    B.Acceptable := by
  have hA1 : B.A1 := by
    intro h
    have hLen := B.length_eq_two_of_order_one D h
    omega
  have hA2 : B.A2 := by
    constructor
    · intro i p hip j hj
      fin_cases i
      · rw [h0] at hip
        cases hip
      · fin_cases j
        · exact Or.inl (by decide)
        · obtain ⟨z, hz, _⟩ := hj
          rw [h1] at hz
          cases hz
        · exact Or.inr (by decide)
      · rw [h2] at hip
        cases hip
    · intro i p u v hip hPrev hNext hDifferent _ _
      fin_cases i
      · rw [h0] at hip
        cases hip
      · have hu : u = x := by
          have h := hPrev
          simpa [trainCyclicPred, h0] using h
        have hv : v = y := by
          have h := hNext
          simpa [cyclicSucc, h2] using h
        rw [hu, hv]
        exact hNoPair
      · rw [h2] at hip
        cases hip
  have hA3 : B.A3 := by
    intro p _
    refine ⟨(2 : Fin 3), ?_⟩
    intro j hj
    fin_cases j
    · exact Or.inr (by decide)
    · obtain ⟨z, hz, _⟩ := hj
      rw [h1] at hz
      cases hz
    · exact Or.inl rfl
  exact ⟨hA1, hA2, hA3⟩

/-- The cyclic rotation with connector shape (wagon w, vertex y,
vertex x) has the analogous automatically acceptable 3-cycle. -/
theorem BigCycle.three_wvv_acceptable
    (B : D.BigCycle 3) (x y : V) (w : P)
    (h0 : B.connector 0 = Sum.inr w)
    (h1 : B.connector 1 = Sum.inl y)
    (h2 : B.connector 2 = Sum.inl x)
    (hNoPair : ¬ D.PairEdge x y) :
    B.Acceptable := by
  have hA1 : B.A1 := by
    intro h
    have hLen := B.length_eq_two_of_order_one D h
    omega
  have hA2 : B.A2 := by
    constructor
    · intro i p hip j hj
      fin_cases i
      · fin_cases j
        · obtain ⟨z, hz, _⟩ := hj
          rw [h0] at hz
          cases hz
        · exact Or.inr (by decide)
        · exact Or.inl (by decide)
      · rw [h1] at hip
        cases hip
      · rw [h2] at hip
        cases hip
    · intro i p u v hip hPrev hNext hDifferent _ _
      fin_cases i
      · have hu : u = x := by
          have h := hPrev
          simpa [trainCyclicPred, h2] using h
        have hv : v = y := by
          have h := hNext
          simpa [cyclicSucc, h1] using h
        rw [hu, hv]
        exact hNoPair
      · rw [h1] at hip
        cases hip
      · rw [h2] at hip
        cases hip
  have hA3 : B.A3 := by
    intro p _
    refine ⟨(1 : Fin 3), ?_⟩
    intro j hj
    fin_cases j
    · obtain ⟨z, hz, _⟩ := hj
      rw [h0] at hz
      cases hz
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  exact ⟨hA1, hA2, hA3⟩


/-- The source of a two-occurrence long replacement has two vertex
connectors, hence twice-order four. -/
theorem BigCycle.two_vertices_twiceOrder
    (C : D.BigCycle 2) (x y : V)
    (h0 : C.connector 0 = Sum.inl x)
    (h1 : C.connector 1 = Sum.inl y) :
    C.twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, Fin.sum_univ_two,
    cyclicSucc, connectorKind, twiceOccurrenceWeight, h0, h1]

/-- One fresh wagon between two original vertices splits one V/V
pair into V/W and W/V without changing twice-order. -/
theorem BigCycle.three_vwv_twiceOrder
    (B : D.BigCycle 3) (x y : V) (w : P)
    (h0 : B.connector 0 = Sum.inl x)
    (h1 : B.connector 1 = Sum.inr w)
    (h2 : B.connector 2 = Sum.inl y) :
    B.twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, Fin.sum_univ_three,
    cyclicSucc, connectorKind, twiceOccurrenceWeight, h0, h1, h2]

/-- The cyclic rotation has the same numerical order. -/
theorem BigCycle.three_wvv_twiceOrder
    (B : D.BigCycle 3) (x y : V) (w : P)
    (h0 : B.connector 0 = Sum.inr w)
    (h1 : B.connector 1 = Sum.inl y)
    (h2 : B.connector 2 = Sum.inl x) :
    B.twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, Fin.sum_univ_three,
    cyclicSucc, connectorKind, twiceOccurrenceWeight, h0, h1, h2]

end StructuralRamsey.Girth.OrderOneData

import Girth.TrainBigCycleOrderOneExtraction

/-!
# Circulation: numerical budget of a labelled big cycle

Every occurrence has twice-weight at least one, so the length of a
big cycle is bounded by twice its order. Consequently order one
forces precisely two occurrences; their boundaries must be mixed.

This proves the elementary reduction stated in the circulated
manuscript without importing any appendix argument.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Every occurrence contributes at least one to twice the order. -/
theorem BigCycle.length_le_twiceOrder
    {n : ℕ} (C : D.BigCycle n) : n ≤ C.twiceOrder := by
  classical
  have h : (∑ i : Fin n, (1 : ℕ)) ≤
      ∑ i : Fin n, twiceOccurrenceWeight
        (connectorKind (C.connector i))
        (connectorKind (C.connector (cyclicSucc i))) := by
    apply Finset.sum_le_sum
    intro i _
    exact twiceOccurrenceWeight_one_le _ _
  simpa [BigCycle.twiceOrder] using h

/-- An order-one big cycle has exactly two occurrences. -/
theorem BigCycle.length_eq_two_of_order_one
    {n : ℕ} (C : D.BigCycle n)
    (h : C.twiceOrder = 2) : n = 2 := by
  have hlen := C.length_le_twiceOrder
  have hmin := C.length_ge_two
  omega

/-- At order one those two occurrences must both be mixed. -/
theorem BigCycle.connectors_mixed_of_order_one
    {n : ℕ} (C : D.BigCycle n)
    (h : C.twiceOrder = 2) :
    ∀ i : Fin n,
      connectorKind (C.connector i) ≠
        connectorKind (C.connector (cyclicSucc i)) := by
  have hn := BigCycle.length_eq_two_of_order_one D C h
  subst n
  have hsum :
      twiceOccurrenceWeight
        (connectorKind (C.connector 0))
        (connectorKind (C.connector 1)) +
      twiceOccurrenceWeight
        (connectorKind (C.connector 1))
        (connectorKind (C.connector 0)) = 2 := by
    simpa [BigCycle.twiceOrder, Fin.sum_univ_two, cyclicSucc]
      using h
  intro i
  fin_cases i <;>
    cases hzero : connectorKind (C.connector 0) <;>
    cases hone : connectorKind (C.connector 1) <;>
    simp_all [twiceOccurrenceWeight, cyclicSucc]

end StructuralRamsey.Girth.OrderOneData

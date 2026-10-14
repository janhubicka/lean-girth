import Girth.TrainBigCycleOrderOneExtraction

/-!
# Circulation: all short-only replacements preserve acceptability

In a short replacement the old cyclic connector sequence does not
change. The A2 and A3 clauses of acceptability depend ONLY on those
connectors and on the unchanged ambient physical edge/wagon relation;
the replacing labels do not occur in either clause.

Thus, once the new sequence is known to be a legal big cycle, all
short-only replacements preserve A2 and A3 automatically. Its
numerical order is unchanged. The only additional condition at order
one is retention of some designated label (A1).

This gives a compact formal reduction for the circulation admissible
replacement lemma. Long replacements, which insert wagon connectors,
require a genuinely separate argument. No appendix is involved.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Two labelled big cycles with identical connector sequences have
exactly the same twice-order, regardless of their occurrence labels. -/
theorem BigCycle.twiceOrder_eq_of_same_connectors
    {n : ℕ} (C B : D.BigCycle n)
    (hConn : ∀ i, B.connector i = C.connector i) :
    B.twiceOrder = C.twiceOrder := by
  unfold BigCycle.twiceOrder
  apply Finset.sum_congr rfl
  intro i _
  rw [hConn i, hConn (cyclicSucc i)]

/-- The wagon-connector acceptability clause A2 depends only on the
connector sequence and ambient physical edges and wagons. -/
theorem BigCycle.A2_of_same_connectors
    {n : ℕ} (C B : D.BigCycle n)
    (hConn : ∀ i, B.connector i = C.connector i)
    (hA2 : C.A2) : B.A2 := by
  unfold BigCycle.A2 BigCycle.InWagonAt at *
  simpa only [hConn] using hA2

/-- The nonconnector-wagon clause A3 likewise depends only on the
connector sequence and the ambient wagon carriers. -/
theorem BigCycle.A3_of_same_connectors
    {n : ℕ} (C B : D.BigCycle n)
    (hConn : ∀ i, B.connector i = C.connector i)
    (hA3 : C.A3) : B.A3 := by
  unfold BigCycle.A3 BigCycle.InWagonAt at *
  simpa only [hConn] using hA3

/-- Full acceptability is preserved by any globally legal short-only
replacement. At order one precisely one designated occurrence must
survive. No other restriction on the new labels is needed for A2/A3. -/
theorem BigCycle.acceptable_of_same_connectors
    {n : ℕ} (C B : D.BigCycle n)
    (hConn : ∀ i, B.connector i = C.connector i)
    (hRetain : C.twiceOrder = 2 →
      ∃ i : Fin n, D.designated (B.label i))
    (hAccept : C.Acceptable) : B.Acceptable := by
  rcases hAccept with ⟨_hA1, hA2, hA3⟩
  refine ⟨?_, BigCycle.A2_of_same_connectors D C B hConn hA2,
    BigCycle.A3_of_same_connectors D C B hConn hA3⟩
  intro hOrder
  exact hRetain ((BigCycle.twiceOrder_eq_of_same_connectors D
    C B hConn).symm.trans hOrder)

end StructuralRamsey.Girth.OrderOneData

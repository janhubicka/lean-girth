import Girth.TrainInsertedConnectorNodup
import Girth.TrainLongBoundaryCollision

/-!
# Circulation: inherited source wagon connectors have no adjacent insertion

The literal source LongValid predicate requires the two ORIGINAL connector
boundaries of a long piece to be VERTICES. Therefore an original WAGON
connector at source occurrence i forbids any long piece at i (its right
boundary would be a wagon), and also at cyclicSucc i (its preceding
boundary would be that wagon).

This tiny geometric observation supplies the missing no-insertion premise
for both actual inherited-wagon neighbouring output positions. It does
not assume output A2/A3/Acceptable or any output wagon linearity.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A source wagon connector cannot be the right boundary of a long
replacement, because a LongValid right boundary must be a vertex. -/
theorem BigCycle.oldWagon_not_long_same
    {n : ℕ} (C : D.BigCycle n)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (i : Fin n) (p : P)
    (hOld : C.connector i = Sum.inr p)
    (e f : E) (w : P) :
    pieces i ≠ .long e w f := by
  intro hPiece
  have hv : C.LongValid D k i e w f :=
    C.longValid_of_piece_eq_long D k i pieces hPlan e f w hPiece
  obtain ⟨_x, y, _hPrev, hHere, _he, _hf, _hne,
    _hpe, _hpf, _hxe, _hyf, _hNoPair⟩ := hv
  have hBad : (Sum.inr p : V ⊕ P) = Sum.inl y :=
    hOld.symm.trans hHere
  cases hBad

/-- A source wagon connector cannot be the LEFT boundary of a long
piece at the next source occurrence. -/
theorem BigCycle.oldWagon_not_long_next
    {n : ℕ} (C : D.BigCycle n)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (i : Fin n) (p : P)
    (hOld : C.connector i = Sum.inr p)
    (e f : E) (w : P) :
    pieces (cyclicSucc i) ≠ .long e w f := by
  intro hPiece
  have hv : C.LongValid D k (cyclicSucc i) e w f :=
    C.longValid_of_piece_eq_long D k (cyclicSucc i)
      pieces hPlan e f w hPiece
  obtain ⟨x, _y, hPrev, _hHere, _he, _hf, _hne,
    _hpe, _hpf, _hxe, _hyf, _hNoPair⟩ := hv
  rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i] at hPrev
  have hBad : (Sum.inr p : V ⊕ P) = Sum.inl x :=
    hOld.symm.trans hPrev
  cases hBad

/-- An inherited wagon has NO new connector inserted immediately before
its own old connector or immediately after it (before the next old
connector). This is exactly the geometric restriction on optional
insertion data needed for inherited-wagon neighbour equations. -/
theorem BigCycle.oldWagon_no_adjacent_insertions
    {n : ℕ} (C : D.BigCycle n)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (i : Fin n) (p : P)
    (hOld : C.connector i = Sum.inr p) :
    C.insertedConnector D pieces i = none ∧
      C.insertedConnector D pieces (cyclicSucc i) = none := by
  constructor
  · cases hp : pieces i with
    | keep => simp [BigCycle.insertedConnector, hp]
    | short e => simp [BigCycle.insertedConnector, hp]
    | long e w f =>
        exact False.elim
          ((C.oldWagon_not_long_same D k pieces hPlan i p hOld e f w) hp)
  · cases hp : pieces (cyclicSucc i) with
    | keep => simp [BigCycle.insertedConnector, hp]
    | short e => simp [BigCycle.insertedConnector, hp]
    | long e w f =>
        exact False.elim
          ((C.oldWagon_not_long_next D k pieces hPlan i p hOld e f w) hp)

end StructuralRamsey.Girth.OrderOneData

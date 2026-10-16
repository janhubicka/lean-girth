import Girth.TrainOutputWagonOrigin
import Girth.TrainA3ContactTransfer
import Girth.TrainA2ContactTransfer
import Girth.TrainInsertedConnectorNodup

/-!
# Circulation: reduce all output A3 splitting to actual long insertions

Every short/kept piece contributes only its old source connector.
Consequently if the oldPos image of consecutive source connectors is
NOT consecutive in the literal expanded output, the NEXT source piece
must be long. Its genuine LongValid witness supplies both original
boundary vertices in the inserted wagon, and that wagon actually
occurs among the output connectors.

The first theorem performs this extraction without any source
A2/A3/linearity premise. The second feeds it into the already checked
conditional A3 transfer theorem: assuming only the ordinary
no-insertion successor equation for oldPos, source Acceptable and
SOURCE wagon linearity give output A3. In particular, neither
output Acceptable nor output wagon linearity is a premise.

The no-insertion successor equation is precisely the remaining
literal finite-list problem in the parallel optional-connector lemmas,
not an assertion silently deduced from relational embedding.
No appendix theorem is involved.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Any failure of consecutive old connector positions to stay
consecutive is witnessed by a GENUINE long source piece inserting an
ACTUAL output wagon over its two old vertex boundaries. This only
requires the no-insertion case of the oldPos successor equation. -/
theorem BigCycle.output_split_has_actual_long_wagon
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hNoInsertSucc : ∀ i : Fin n,
      C.insertedConnector D pieces (cyclicSucc i) = none →
        oldPos (cyclicSucc i) = cyclicSucc (oldPos i))
    (i : Fin n)
    (hSplit : oldPos (cyclicSucc i) ≠ cyclicSucc (oldPos i)) :
    ∃ (q : P) (x y : V),
      C.connector i = Sum.inl x ∧
      C.connector (cyclicSucc i) = Sum.inl y ∧
      D.WagonVertex q x ∧ D.WagonVertex q y ∧
      ∃ j : Fin m, B.connector j = Sum.inr q := by
  have hNew : C.insertedConnector D pieces (cyclicSucc i) ≠ none := by
    intro hNone
    exact hSplit (hNoInsertSucc i hNone)
  cases hp : pieces (cyclicSucc i) with
  | keep =>
      have hNone : C.insertedConnector D pieces (cyclicSucc i) = none := by
        simp [BigCycle.insertedConnector, hp]
      exact False.elim (hNew hNone)
  | short e =>
      have hNone : C.insertedConnector D pieces (cyclicSucc i) = none := by
        simp [BigCycle.insertedConnector, hp]
      exact False.elim (hNew hNone)
  | long e q f =>
      have hLong : C.LongValid D k (cyclicSucc i) e q f :=
        C.longValid_of_piece_eq_long D k (cyclicSucc i)
          pieces hPlan e f q hp
      obtain ⟨w, x, y, hPrev, hHere, hWx, hWy, j, hBj⟩ :=
        C.selected_long_A3_split_witness D B pieces hWord
          k (cyclicSucc i) e f q hp hLong
      rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i] at hPrev
      exact ⟨w, x, y, hPrev, hHere, hWx, hWy, j, hBj⟩

/-- The complete source-to-output A3 conclusion reduces to one
finite-list equation: when no wagon is inserted in the NEXT block,
the old right connector of that block is the cyclic successor of
the present old right connector in the output.

All other hypotheses are the literal oldPos/vertex provenance, source
Acceptable and SOURCE linearity already required by the circulation
replacement argument. No output A3, output linearity or output cycle
acceptability is assumed. -/
theorem BigCycle.output_A3_of_noInsertionSuccessor
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (hVertexPos : ∀ (j : Fin m) (x : V),
      B.connector j = Sum.inl x →
        ∃ i : Fin n, j = oldPos i)
    (hNoInsertSucc : ∀ i : Fin n,
      C.insertedConnector D pieces (cyclicSucc i) = none →
        oldPos (cyclicSucc i) = cyclicSucc (oldPos i)) :
    B.A3 := by
  apply C.A3_of_preserved_contacts_and_insertions
    D B oldPos hAccept.2.2 hLinear hConnector
  · exact C.wagon_contacts_pullback_of_vertex_positions
      D B oldPos hConnector hVertexPos
  · intro i hSplit
    exact C.output_split_has_actual_long_wagon
      D B k pieces hPlan hWord oldPos hNoInsertSucc i hSplit

end StructuralRamsey.Girth.OrderOneData

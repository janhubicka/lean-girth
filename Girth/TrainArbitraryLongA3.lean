import Girth.TrainLiteralOldPosA3
import Girth.TrainA3ContactTransfer
import Girth.TrainOutputWagonOrigin
import Girth.TrainInsertedConnectorNodup

/-!
# Circulation: arbitrary long replacements preserve A3

For the non-supreme version of admissible replacement, different
replacement pieces need not use edges from one chosen supreme copy.
The A3 argument does not need that restriction. It only uses:
* the literal expanded connector word and its original vertex positions;
* freshness of every newly inserted wagon;
* both old boundary vertices belonging to that wagon.

The same linearity obstruction forbids an inserted wagon from splitting
two old contacts of a different nonconnector wagon. The theorem below
therefore proves A3 for arbitrary local geometric long replacements
with an ACTUAL legal output BigCycle. No PlanValid, single selected
label, output A2/A3, or appendix theorem is assumed.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Only the physical conditions of a long replacement used by A3.
Unlike LongValid, no designated source label or edge membership in
one supreme copy is required. -/
def BigCycle.LocalLongBoundaryGeometry
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) : Prop :=
  ∀ (i : Fin n) (e f : E) (p : P),
    pieces i = .long e p f →
    ∃ x y : V,
      C.connector (trainCyclicPred i) = Sum.inl x ∧
      C.connector i = Sum.inl y ∧
      D.WagonVertex p x ∧ D.WagonVertex p y

/-- When old connector positions fail to remain consecutive, an
actual fresh long replacement covers both original boundary vertices.
The lemma requires no PlanValid and no output acceptability. -/
theorem BigCycle.arbitrary_long_split_geometry
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongBoundaryGeometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (i : Fin n)
    (hSplit : oldPos (cyclicSucc i) ≠ cyclicSucc (oldPos i)) :
    ∃ (q : P) (x y : V),
      C.connector i = Sum.inl x ∧
      C.connector (cyclicSucc i) = Sum.inl y ∧
      D.WagonVertex q x ∧ D.WagonVertex q y ∧
      ∃ j : Fin m, B.connector j = Sum.inr q := by
  have hInserted : C.insertedConnector D pieces (cyclicSucc i) ≠ none := by
    intro hNone
    exact hSplit (C.literal_oldPos_successor_of_noInsertion
      D B pieces hFresh hWord oldPos hConnector i hNone)
  cases hp : pieces (cyclicSucc i) with
  | keep =>
      exact False.elim (hInserted (by
        simp [BigCycle.insertedConnector, hp]))
  | short e =>
      exact False.elim (hInserted (by
        simp [BigCycle.insertedConnector, hp]))
  | long e p f =>
      obtain ⟨x, y, hPrev, hHere, hPx, hPy⟩ :=
        hGeom (cyclicSucc i) e f p hp
      rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i] at hPrev
      obtain ⟨j, hj⟩ :=
        C.selected_long_wagon_occurs_in_output
          D B pieces hWord (cyclicSucc i) e f p hp
      exact ⟨p, x, y, hPrev, hHere, hPx, hPy, j, hj⟩

/-- (A3) survives arbitrary simultaneous replacement with locally
valid long-piece boundary geometry. Its proof is independent of A1,
A2, the label provenance of the new edges, and the special strict
supreme-plan hypothesis. -/
theorem BigCycle.output_A3_of_arbitrary_long_geometry
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hA3 : C.A3) (hLinear : D.LinearPretrain)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongBoundaryGeometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces) :
    B.A3 := by
  obtain ⟨oldPos, hConnector, hVertexPos⟩ :=
    C.oldPos_exists_of_literal_resultWord D B pieces hWord
  apply C.A3_of_preserved_contacts_and_insertions
    D B oldPos hA3 hLinear hConnector
  · exact C.wagon_contacts_pullback_of_vertex_positions
      D B oldPos hConnector hVertexPos
  · intro i hSplit
    exact C.arbitrary_long_split_geometry
      D B pieces hGeom hFresh hWord oldPos hConnector i hSplit

end StructuralRamsey.Girth.OrderOneData

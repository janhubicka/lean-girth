import Girth.TrainPlanGlobalAssembly
import Girth.TrainBigCycleOrderBudget
import Mathlib.Tactic

/-!
# Circulation: A1 follows automatically for expanded cycles of length ≥ 3

Every actual piece word has length one or two. In particular, a replacement
plan NEVER decreases the number of occurrences. This observation has already
been checked in TrainPlanGlobalAssembly.

Consequently, when a source BigCycle has at least three occurrences, any
literal globally legal output word also has at least three occurrences;
its order cannot be one by the checked length-versus-order lemma.
Therefore the new A1 designation condition is VACUOUS.

No chosen supreme label or existing output acceptability is assumed.
This short lemma discharges the A1 component of the future simultaneous
replacement acceptability theorem at source length ≥ 3. The remaining
A2/A3 conditions, order preservation, and composition are separate.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- An expanded replacement cycle has at least as many occurrences as the
source, because the literal output word is a concatenation of nonempty pieces. -/
theorem BigCycle.output_length_ge_source
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun i : Fin m =>
      (B.label i, B.connector i)) = C.resultWord D pieces) :
    n ≤ m := by
  have h := C.resultWord_length_ge_source D pieces
  rw [← hWord] at h
  simpa using h

/-- A1 on the actual expanded output word of any source cycle having at
least three occurrences. Neither output A2/A3 nor designation retention is
needed, because an output cycle of length ≥ 3 cannot have order one. -/
theorem BigCycle.output_A1_of_source_length_three
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hn : 3 ≤ n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun i : Fin m =>
      (B.label i, B.connector i)) = C.resultWord D pieces) :
    B.A1 := by
  intro hOrder
  have hm : n ≤ m :=
    C.output_length_ge_source D B pieces hWord
  have hTwo : m = 2 := B.length_eq_two_of_order_one D hOrder
  omega

end StructuralRamsey.Girth.OrderOneData

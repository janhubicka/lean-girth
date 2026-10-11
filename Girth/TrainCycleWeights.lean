import Mathlib.Tactic

/-!
# Numerical order under deletion of internal big-cycle connectors

An occurrence with two equal connector kinds (vertex/vertex or
wagon/wagon) contributes 1 to the big-cycle order; a mixed occurrence
contributes 1/2. We work at twice the order to avoid rationals.

Deleting a connector between two consecutive occurrences merges their
two boundary-kind pairs. The joined occurrence contributes no more
than their total contribution, irrespective of which kind the
deleted connector had. Applying this locally at each deletion
proves the numerical inequality in the circulation reduct lemma.

This verifies ONLY the order budget. It does not establish that the
reduct is a legal big cycle, that connectors stay distinct, or any
acceptability condition (A1)--(A3).
-/

namespace StructuralRamsey.Girth

/-- The two types of connectors of a big cycle. -/
inductive CycleConnectorKind where
  | vertex
  | wagon
  deriving DecidableEq, Repr

/-- Twice the contribution of one occurrence to the cycle order. -/
def twiceOccurrenceWeight (left right : CycleConnectorKind) : ℕ :=
  if left = right then 2 else 1

theorem twiceOccurrenceWeight_one_le
    (left right : CycleConnectorKind) :
    1 ≤ twiceOccurrenceWeight left right := by
  cases left <;> cases right <;> decide

theorem twiceOccurrenceWeight_le_two
    (left right : CycleConnectorKind) :
    twiceOccurrenceWeight left right ≤ 2 := by
  cases left <;> cases right <;> decide

/-- Replacing two consecutive occurrences by one cannot increase
twice the order. This is the local inequality used when internal
connectors are deleted in the reduction to the witness. -/
theorem twiceOccurrenceWeight_join_le
    (left middle right : CycleConnectorKind) :
    twiceOccurrenceWeight left right ≤
      twiceOccurrenceWeight left middle +
      twiceOccurrenceWeight middle right := by
  cases left <;> cases middle <;> cases right <;> decide

/-- The two-deletion version, useful for a three-occurrence segment. -/
theorem twiceOccurrenceWeight_join_three_le
    (a b c d : CycleConnectorKind) :
    twiceOccurrenceWeight a d ≤
      twiceOccurrenceWeight a b +
      twiceOccurrenceWeight b c +
      twiceOccurrenceWeight c d := by
  have h₁ := twiceOccurrenceWeight_join_le a b d
  have h₂ := twiceOccurrenceWeight_join_le b c d
  omega

end StructuralRamsey.Girth

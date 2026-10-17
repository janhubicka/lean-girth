import Girth.TrainOptionalKindChain
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Circulation: cyclic List weight as a sum of adjacent connector pairs

A list of connector kinds has a canonical numerical cyclic weight:
enter at its final connector and read the list once. For a nonempty
list this equals the sum of the pair weights of successive connectors
in the list, including the last-to-first pair.

We prove the equality using Mathlib's one-step list rotation and an
elementary zipWith terminal-edge lemma. This establishes the pure
List identity needed to transport optional insertion weights to the
manuscript's finite-indexed BigCycle order.

This module uses no geometric assumptions or appendix theorem.
-/

namespace StructuralRamsey.Girth

/-- Last element of a nonempty list written as its first entry and
remaining tail, without a default Kind instance. -/
def kindLastOr (a : CycleConnectorKind) : List CycleConnectorKind →
    CycleConnectorKind
  | [] => a
  | b :: rest => kindLastOr b rest

theorem getLast?_cons_eq_kindLastOr
    (a : CycleConnectorKind) (rest : List CycleConnectorKind) :
    (a :: rest).getLast? = some (kindLastOr a rest) := by
  induction rest generalizing a with
  | nil => rfl
  | cons b more ih =>
      simpa [kindLastOr] using ih b

/-- The zipper of a walk shifted by one and closed at an arbitrary
terminal connector has exactly one extra closing edge. -/
theorem zipWeight_append_terminal
    (a terminal : CycleConnectorKind)
    (tail : List CycleConnectorKind) :
    (List.zipWith twiceOccurrenceWeight
      (a :: tail) (tail ++ [terminal])).sum =
    (List.zipWith twiceOccurrenceWeight
      (a :: tail) tail).sum +
        twiceOccurrenceWeight (kindLastOr a tail) terminal := by
  induction tail generalizing a with
  | nil =>
      simp [kindLastOr]
  | cons b rest ih =>
      simpa [List.zipWith, kindLastOr, ih b, Nat.add_assoc]

/-- The opened walk's twice-weight is the sum of the adjacent
pairs of the two lists obtained by prefixing its entering vertex. -/
theorem twiceSegmentWeight_eq_zipWeight
    (enter : CycleConnectorKind)
    (tail : List CycleConnectorKind) :
    twiceSegmentWeight enter tail =
      (List.zipWith twiceOccurrenceWeight (enter :: tail) tail).sum := by
  induction tail generalizing enter with
  | nil => rfl
  | cons b rest ih =>
      simpa [twiceSegmentWeight, List.zipWith, ih b]

/-- Cyclic twice-weight is precisely the zip sum against the list
rotated once to the left. This includes empty and singleton lists. -/
theorem cyclicKindTwiceWeight_eq_zipRotate
    (word : List CycleConnectorKind) :
    cyclicKindTwiceWeight word =
      (List.zipWith twiceOccurrenceWeight
        word (word.rotate 1)).sum := by
  cases word with
  | nil =>
      simp [cyclicKindTwiceWeight]
  | cons a tail =>
      have hLast := getLast?_cons_eq_kindLastOr a tail
      have hRotate : (a :: tail).rotate 1 = tail ++ [a] := by
        simpa using (List.rotate_cons_succ tail a 0)
      have hZip := zipWeight_append_terminal a a tail
      have hSegment := twiceSegmentWeight_eq_zipWeight a tail
      simp only [cyclicKindTwiceWeight, hLast, hRotate]
      change twiceSegmentWeight (kindLastOr a tail) (a :: tail) =
        (List.zipWith twiceOccurrenceWeight
          (a :: tail) (tail ++ [a])).sum
      calc
        twiceSegmentWeight (kindLastOr a tail) (a :: tail) =
          twiceOccurrenceWeight (kindLastOr a tail) a +
            twiceSegmentWeight a tail := rfl
        _ = twiceOccurrenceWeight (kindLastOr a tail) a +
              (List.zipWith twiceOccurrenceWeight
                (a :: tail) tail).sum := by
                rw [hSegment]
        _ = (List.zipWith twiceOccurrenceWeight
              (a :: tail) (tail ++ [a])).sum := by
                omega

end StructuralRamsey.Girth

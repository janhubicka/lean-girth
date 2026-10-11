import Girth.TrainCycleWeights

/-!
# Cycle-order nonincrease through an arbitrary finite segment

The checked two-occurrence inequality extends by induction to
any finite list of intermediate connector kinds. The new lemma
exactly matches the numerical part of replacing a whole segment
by one occurrence with the same two boundary connector kinds.
It does not show the new sequence forms a legal big cycle or that
acceptability (A1)--(A3) survives.
-/

namespace StructuralRamsey.Girth

/-- Sum of twice-occurrence weights for the consecutive connectors
left, then every connector in the list. Empty means weight zero. -/
def twiceSegmentWeight (left : CycleConnectorKind) :
    List CycleConnectorKind → ℕ
  | [] => 0
  | c :: cs => twiceOccurrenceWeight left c +
      twiceSegmentWeight c cs

/-- Collapsing an arbitrary finite block of consecutive occurrences
to the one occurrence with the same boundary kinds does not increase
the numerical big-cycle order. -/
theorem twiceOccurrenceWeight_segment_le
    (right : CycleConnectorKind)
    (middle : List CycleConnectorKind) :
    ∀ left : CycleConnectorKind,
      twiceOccurrenceWeight left right ≤
        twiceSegmentWeight left (middle ++ [right]) := by
  induction middle with
  | nil =>
      intro left
      simp [twiceSegmentWeight]
  | cons mid tail ih =>
      intro left
      change twiceOccurrenceWeight left right ≤
        twiceOccurrenceWeight left mid +
          twiceSegmentWeight mid (tail ++ [right])
      calc
        twiceOccurrenceWeight left right ≤
            twiceOccurrenceWeight left mid +
              twiceOccurrenceWeight mid right :=
          twiceOccurrenceWeight_join_le left mid right
        _ ≤ twiceOccurrenceWeight left mid +
              twiceSegmentWeight mid (tail ++ [right]) :=
          Nat.add_le_add_left (ih mid) _

end StructuralRamsey.Girth

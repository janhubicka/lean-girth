import Girth.TrainCycleSegmentWeight

/-!
# Circulation: arbitrary simultaneous long-piece expansions preserve order

A long piece e⁺ W f⁺ replaces an occurrence with two vertex boundaries
by two mixed occurrences. Its connector-kind word therefore inserts
a WAGON between two consecutive VERTEX connectors, replacing weight 2
by 1+1 and leaving the surrounding weights unchanged.

We formalize arbitrary insertions at arbitrary positions of a finite
connector-kind walk, and their iterated closure. The resulting theorem
proves the full NUMERICAL order preservation of simultaneous long
replacements (and hence of the numerical part of the manuscript's
replacement lemma). Distinctness, A1--A3 and global legal big cycles
are handled separately by the circulation cycle language.

No appendix definitions or claims are used here.
-/

namespace StructuralRamsey.Girth

/-- Insert precisely one wagon connector between two successive
vertex connectors. The prefix rule allows insertion at any position
in a walk of connector kinds. -/
inductive LongPieceConnectorInsertion :
    List CycleConnectorKind → List CycleConnectorKind → Prop where
  | vertex (tail : List CycleConnectorKind) :
      LongPieceConnectorInsertion
        (.vertex :: .vertex :: tail)
        (.vertex :: .wagon :: .vertex :: tail)
  | prepend (head : CycleConnectorKind)
      {before after : List CycleConnectorKind}
      (h : LongPieceConnectorInsertion before after) :
      LongPieceConnectorInsertion (head :: before) (head :: after)

/-- A single legitimate long expansion preserves the total twice-order
of a connector path, including its specified entering connector. -/
theorem LongPieceConnectorInsertion.preserves_twiceWeight
    {before after : List CycleConnectorKind}
    (h : LongPieceConnectorInsertion before after)
    (enter : CycleConnectorKind) :
    twiceSegmentWeight enter before =
      twiceSegmentWeight enter after := by
  induction h generalizing enter with
  | vertex tail =>
      simp [twiceSegmentWeight, twiceOccurrenceWeight] <;> omega
  | @prepend head before after h ih =>
      change
        twiceOccurrenceWeight enter head +
          twiceSegmentWeight head before =
        twiceOccurrenceWeight enter head +
          twiceSegmentWeight head after
      rw [ih head]

/-- Any finite sequence of legitimate long expansions. The source
and target are explicit lists, so no arbitrary rewriting is hidden. -/
inductive LongPieceConnectorExpansions :
    List CycleConnectorKind → List CycleConnectorKind → Prop where
  | refl (word : List CycleConnectorKind) :
      LongPieceConnectorExpansions word word
  | step {before middle after : List CycleConnectorKind}
      (h : LongPieceConnectorInsertion before middle)
      (tail : LongPieceConnectorExpansions middle after) :
      LongPieceConnectorExpansions before after

/-- Replacing any collection of vertex/vertex occurrences by
vertex/wagon/vertex long pieces preserves the entire numerical
twice-order, independent of insertion positions or their order. -/
theorem LongPieceConnectorExpansions.preserves_twiceWeight
    {before after : List CycleConnectorKind}
    (h : LongPieceConnectorExpansions before after)
    (enter : CycleConnectorKind) :
    twiceSegmentWeight enter before =
      twiceSegmentWeight enter after := by
  induction h with
  | refl word =>
      rfl
  | step h tail ih =>
      exact (h.preserves_twiceWeight enter).trans ih

end StructuralRamsey.Girth

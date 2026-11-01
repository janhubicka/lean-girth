import Girth.TrainDesignatedLabelLexRank
import Mathlib.Data.List.OfFn

/-!
# Target-independent designated-count rank on actual circulation BigCycles

Lift the raw list counting kernel to the actual typed BigCycle label
functions. A literal decomposition of a source/output replacement
word into an unchanged prefix/suffix and the replaced source block
immediately yields a strict drop of designated occurrence count.

This does not assume a reduced supreme target or old B-copy label;
designated means precisely Sum.inl. The remaining nontrivial
integration is to derive the required list decompositions from
BigCycle.resultWord / onlyLongPieces for a real fresh insertion.
No appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Count designated occurrence LABELS of a literal BigCycle.
This is not the number of distinct designated copies, nor the
number of source segment owners: repeated designated labels are
counted with their occurrences. -/
noncomputable def BigCycle.designatedOccurrenceCount
    {n : ℕ} (C : D.BigCycle n) : ℕ :=
  designatedLabelCount (List.ofFn C.label)

/-- Given exact source/output label-list decompositions for a
one-long block, the designated-count rank of the actual output
BigCycle drops exactly one. No output length equality is needed. -/
theorem BigCycle.designatedCount_drop_of_long_literal
    {n m : ℕ} (C : D.BigCycle n) (H : D.BigCycle m)
    (before after : List (I ⊕ E))
    (source : I) (first second : E)
    (hSource : List.ofFn C.label =
      before ++ Sum.inl source :: after)
    (hOutput : List.ofFn H.label =
      before ++ Sum.inr first :: Sum.inr second :: after) :
    H.designatedOccurrenceCount D + 1 =
      C.designatedOccurrenceCount D := by
  change designatedLabelCount (List.ofFn H.label) + 1 =
    designatedLabelCount (List.ofFn C.label)
  rw [hSource, hOutput]
  exact designatedLabelCount_long_insert_drop
    before after source first second

/-- The parallel actual-cycle statement for a single designated
SHORT replacement. Again this is exact literal label accounting,
not a statement about owner-cut decrease. -/
theorem BigCycle.designatedCount_drop_of_short_literal
    {n m : ℕ} (C : D.BigCycle n) (H : D.BigCycle m)
    (before after : List (I ⊕ E))
    (source : I) (edge : E)
    (hSource : List.ofFn C.label =
      before ++ Sum.inl source :: after)
    (hOutput : List.ofFn H.label =
      before ++ Sum.inr edge :: after) :
    H.designatedOccurrenceCount D + 1 =
      C.designatedOccurrenceCount D := by
  change designatedLabelCount (List.ofFn H.label) + 1 =
    designatedLabelCount (List.ofFn C.label)
  rw [hSource, hOutput]
  exact designatedLabelCount_short_replace_drop
    before after source edge

end StructuralRamsey.Girth.OrderOneData

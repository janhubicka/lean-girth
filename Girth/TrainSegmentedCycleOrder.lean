import Girth.TrainFinCyclicOrder
import Mathlib.Tactic

/-!
# Circulation: cyclic order under arbitrary simultaneous segment contraction

Section 12 reduces a big cycle to the witness by contracting *several*
consecutive standard-copy segments at once. The existing
\`twiceOccurrenceWeight_segment_le\` controls one segment. This module
checks the global arithmetic, including the closing edge of the cyclic
word, for any finite sequence of segments.

A segment is represented by its internal connector kinds followed by
its final boundary kind. Both source and reduct retain every final
boundary, so local segment inequalities can be summed without any
disjointness or length assumptions beyond the representation itself.

This is the NUMERICAL part of the witness-reduction lemma only:
legality of the contracted big cycle, distinct physical connectors,
A1--A3, and the geometrical segmentation are separate obligations.
No appendix theorem is used.
-/

namespace StructuralRamsey.Girth

/-- Internal connector kinds and the retained right boundary of one segment. -/
abbrev CycleReductionBlock := List CycleConnectorKind × CycleConnectorKind

/-- The boundary word after contracting each segment to one occurrence. -/
def reducedSegmentWord : List CycleReductionBlock → List CycleConnectorKind
  | [] => []
  | (_, right) :: tail => right :: reducedSegmentWord tail

/-- The original expanded word with every segment's internal connectors. -/
def expandedSegmentWord : List CycleReductionBlock → List CycleConnectorKind
  | [] => []
  | (middle, right) :: tail =>
      (middle ++ [right]) ++ expandedSegmentWord tail

/-- Sum of the reduced occurrence weights, entering at a given boundary. -/
def twiceReducedSegmentBudget :
    CycleConnectorKind → List CycleReductionBlock → ℕ
  | _, [] => 0
  | left, (_, right) :: tail =>
      twiceOccurrenceWeight left right +
        twiceReducedSegmentBudget right tail

/-- Sum of the source occurrence weights, segment by segment. -/
def twiceExpandedSegmentBudget :
    CycleConnectorKind → List CycleReductionBlock → ℕ
  | _, [] => 0
  | left, (middle, right) :: tail =>
      twiceSegmentWeight left (middle ++ [right]) +
        twiceExpandedSegmentBudget right tail

/-- Splitting an opened connector word preserves its twice-weight. -/
theorem twiceSegmentWeight_append_path
    (left : CycleConnectorKind)
    (before after : List CycleConnectorKind) :
    twiceSegmentWeight left (before ++ after) =
      twiceSegmentWeight left before +
        twiceSegmentWeight (kindLastOr left before) after := by
  induction before generalizing left with
  | nil => rfl
  | cons first rest ih =>
      change twiceOccurrenceWeight left first +
          twiceSegmentWeight first (rest ++ after) =
        (twiceOccurrenceWeight left first +
          twiceSegmentWeight first rest) +
          twiceSegmentWeight (kindLastOr first rest) after
      rw [ih first]
      omega

/-- Each expanded segment ends at its prescribed right boundary. -/
theorem kindLastOr_segment
    (left right : CycleConnectorKind)
    (middle : List CycleConnectorKind) :
    kindLastOr left (middle ++ [right]) = right := by
  induction middle generalizing left with
  | nil => rfl
  | cons first rest ih =>
      change kindLastOr first (rest ++ [right]) = right
      exact ih first

/-- The recursive reduced sum equals the weight of the literal reduct word. -/
theorem twiceReducedSegmentBudget_eq_word
    (blocks : List CycleReductionBlock) :
    ∀ left : CycleConnectorKind,
      twiceReducedSegmentBudget left blocks =
        twiceSegmentWeight left (reducedSegmentWord blocks) := by
  induction blocks with
  | nil =>
      intro left
      rfl
  | cons block rest ih =>
      intro left
      rcases block with ⟨middle, right⟩
      change twiceOccurrenceWeight left right +
          twiceReducedSegmentBudget right rest =
        twiceOccurrenceWeight left right +
          twiceSegmentWeight right (reducedSegmentWord rest)
      rw [← ih right]

/-- The recursive expanded sum equals the weight of the literal source word. -/
theorem twiceExpandedSegmentBudget_eq_word
    (blocks : List CycleReductionBlock) :
    ∀ left : CycleConnectorKind,
      twiceExpandedSegmentBudget left blocks =
        twiceSegmentWeight left (expandedSegmentWord blocks) := by
  induction blocks with
  | nil =>
      intro left
      rfl
  | cons block rest ih =>
      intro left
      rcases block with ⟨middle, right⟩
      change twiceSegmentWeight left (middle ++ [right]) +
          twiceExpandedSegmentBudget right rest =
        twiceSegmentWeight left
          ((middle ++ [right]) ++ expandedSegmentWord rest)
      rw [twiceSegmentWeight_append_path left
        (middle ++ [right]) (expandedSegmentWord rest)]
      rw [kindLastOr_segment]
      rw [← ih right]

/-- Arbitrarily many disjoint consecutive segment contractions do not
increase the total twice-weight, even with different block lengths. -/
theorem twiceReducedSegmentBudget_le_expanded
    (blocks : List CycleReductionBlock) :
    ∀ left : CycleConnectorKind,
      twiceReducedSegmentBudget left blocks ≤
        twiceExpandedSegmentBudget left blocks := by
  induction blocks with
  | nil =>
      intro left
      exact Nat.le_refl 0
  | cons block rest ih =>
      intro left
      rcases block with ⟨middle, right⟩
      change twiceOccurrenceWeight left right +
          twiceReducedSegmentBudget right rest ≤
        twiceSegmentWeight left (middle ++ [right]) +
          twiceExpandedSegmentBudget right rest
      exact Nat.add_le_add
        (twiceOccurrenceWeight_segment_le right middle left)
        (ih right)

/-- Literal opened-word form: no numerical cost comes from merging
arbitrarily many consecutive segments of a cycle. -/
theorem twiceReducedSegmentWord_le_expanded
    (blocks : List CycleReductionBlock)
    (left : CycleConnectorKind) :
    twiceSegmentWeight left (reducedSegmentWord blocks) ≤
      twiceSegmentWeight left (expandedSegmentWord blocks) := by
  rw [← twiceReducedSegmentBudget_eq_word blocks left,
      ← twiceExpandedSegmentBudget_eq_word blocks left]
  exact twiceReducedSegmentBudget_le_expanded blocks left

/-- Cyclic form, including the final-to-first occurrence. The hypotheses
identify the common last boundary; proving they hold for a *geometric*
minimum segmentation belongs to the remaining reduct construction. -/
theorem cyclicReducedSegmentWord_le_expanded
    (blocks : List CycleReductionBlock)
    (closing : CycleConnectorKind)
    (hReducedLast : (reducedSegmentWord blocks).getLast? = some closing)
    (hExpandedLast : (expandedSegmentWord blocks).getLast? = some closing) :
    cyclicKindTwiceWeight (reducedSegmentWord blocks) ≤
      cyclicKindTwiceWeight (expandedSegmentWord blocks) := by
  simp only [cyclicKindTwiceWeight, hReducedLast, hExpandedLast]
  exact twiceReducedSegmentWord_le_expanded blocks closing



/-- Replacing each nonempty segment by its retained terminal connector
does not increase the number of occurrences. -/
theorem reducedSegmentWord_length_le_expanded
    (blocks : List CycleReductionBlock) :
    (reducedSegmentWord blocks).length ≤
      (expandedSegmentWord blocks).length := by
  induction blocks with
  | nil => exact Nat.le_refl 0
  | cons block rest ih =>
      rcases block with ⟨middle, right⟩
      change (right :: reducedSegmentWord rest).length ≤
        ((middle ++ [right]) ++ expandedSegmentWord rest).length
      simp only [List.length_cons, List.length_append,
        List.length_singleton]
      omega

namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Numerical conclusion for two ACTUAL big cycles whose cyclic connector
words are related by a finite geometric segment decomposition. This is the
direct bridge from the List inequality to Section 12's order budget.
It assumes (rather than constructs) the reduct big cycle and connector words. -/
theorem BigCycle.reduct_twiceOrder_le_of_segmented_words
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (blocks : List CycleReductionBlock)
    (hSource : List.ofFn (fun i : Fin n =>
      connectorKind (C.connector i)) = expandedSegmentWord blocks)
    (hReduct : List.ofFn (fun j : Fin m =>
      connectorKind (B.connector j)) = reducedSegmentWord blocks)
    (closing : CycleConnectorKind)
    (hReducedLast : (reducedSegmentWord blocks).getLast? = some closing)
    (hExpandedLast : (expandedSegmentWord blocks).getLast? = some closing) :
    B.twiceOrder ≤ C.twiceOrder := by
  rw [B.twiceOrder_eq_cyclicKindList D,
      C.twiceOrder_eq_cyclicKindList D,
      hReduct, hSource]
  exact cyclicReducedSegmentWord_le_expanded
    blocks closing hReducedLast hExpandedLast


/-- Length part of the circulated reduct lemma, provided the source and
reduct have the indicated literal connector-kind segmentation. -/
theorem BigCycle.reduct_length_le_of_segmented_words
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (blocks : List CycleReductionBlock)
    (hSource : List.ofFn (fun i : Fin n =>
      connectorKind (C.connector i)) = expandedSegmentWord blocks)
    (hReduct : List.ofFn (fun j : Fin m =>
      connectorKind (B.connector j)) = reducedSegmentWord blocks) :
    m ≤ n := by
  have hn : n = (expandedSegmentWord blocks).length := by
    simpa using congrArg List.length hSource
  have hm : m = (reducedSegmentWord blocks).length := by
    simpa using congrArg List.length hReduct
  have h := reducedSegmentWord_length_le_expanded blocks
  omega

end OrderOneData

end StructuralRamsey.Girth

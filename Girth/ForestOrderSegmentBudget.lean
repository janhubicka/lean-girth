import Girth.TrainSegmentedCycleOrder
import Girth.ForestToSupremeCycle

/-!
# The segment-count budget for forest-to-order conversion

The forest hypothesis is indexed by the number of distinct members, whereas
the source-cycle bound is its order.  A mixed singleton segment has weight
one half, so order alone cannot bound the number of segments.  Once those
singletons have been excluded, each segment has weight at least one: a
singleton has equal boundary kinds, and a longer segment contains at least
two occurrences of weight at least one half.

This module proves the resulting cyclic budget, including its closing
boundary, and applies it to an actual acceptable reduced bottom cycle.  The
source and reduct may belong to different incidence data.  Their literal
connector-word identities and the absence of mixed singletons are explicit
geometric inputs; no minimal-segmentation or cycle-transfer theorem is
assumed to follow from this arithmetic.  In particular an order-one reduct
without A1 must instead use the separate two-member bridge theorem.
-/

namespace StructuralRamsey.Girth

/-- Every occurrence contributes at least one to twice the segment weight. -/
theorem length_le_twiceSegmentWeight
    (word : List CycleConnectorKind) :
    ∀ left : CycleConnectorKind,
      word.length ≤ twiceSegmentWeight left word := by
  induction word with
  | nil => intro left; exact Nat.le_refl 0
  | cons first rest ih =>
      intro left
      have hw := twiceOccurrenceWeight_one_le left first
      have hr := ih first
      simp only [List.length_cons, twiceSegmentWeight]
      omega

/-- A nonsingleton segment, or a singleton with equal boundary kinds, has
weight at least one.  A mixed singleton is exactly the excluded case. -/
theorem two_le_twiceSegmentWeight_of_not_mixed_singleton
    (left right : CycleConnectorKind) (middle : List CycleConnectorKind)
    (hNoMixed : middle = [] → left = right) :
    2 ≤ twiceSegmentWeight left (middle ++ [right]) := by
  cases middle with
  | nil =>
      have h := hNoMixed rfl
      simp [twiceSegmentWeight, twiceOccurrenceWeight, h]
  | cons first rest =>
      have h := length_le_twiceSegmentWeight ((first :: rest) ++ [right]) left
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      omega

/-- Adjacent segments share their boundary kind.  At every singleton the
incoming and outgoing kinds agree.  The incoming kind for a cyclic word is
its actual final boundary, not an arbitrary default. -/
def NoMixedSingletonSegments :
    CycleConnectorKind → List CycleReductionBlock → Prop
  | _, [] => True
  | left, (middle, right) :: rest =>
      (middle = [] → left = right) ∧ NoMixedSingletonSegments right rest

/-- Summing the segment lower bounds counts every source occurrence exactly
once through the existing expanded segment budget. -/
theorem twice_segmentCount_le_expandedBudget
    (blocks : List CycleReductionBlock) :
    ∀ left : CycleConnectorKind, NoMixedSingletonSegments left blocks →
      2 * blocks.length ≤ twiceExpandedSegmentBudget left blocks := by
  induction blocks with
  | nil => intro left h; exact Nat.le_refl 0
  | cons block rest ih =>
      intro left h
      rcases block with ⟨middle, right⟩
      obtain ⟨hHere, hRest⟩ := h
      have hWeight := two_le_twiceSegmentWeight_of_not_mixed_singleton
        left right middle hHere
      have hTail := ih right hRest
      simp only [List.length_cons, twiceExpandedSegmentBudget]
      omega

@[simp] theorem reducedSegmentWord_length_eq
    (blocks : List CycleReductionBlock) :
    (reducedSegmentWord blocks).length = blocks.length := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      rcases block with ⟨middle, right⟩
      simpa [reducedSegmentWord] using congrArg Nat.succ ih

/-- The segment-count estimate for the literal cyclic source word.  Its
closing kind is derived from the segmentation, including the empty case. -/
theorem twice_segmentCount_le_cyclicExpandedWeight
    (blocks : List CycleReductionBlock)
    (hNoMixed : NoMixedSingletonSegments
      (kindLastOr .vertex (reducedSegmentWord blocks)) blocks) :
    2 * blocks.length ≤ cyclicKindTwiceWeight (expandedSegmentWord blocks) := by
  by_cases hEmpty : blocks = []
  · subst blocks
    simp [expandedSegmentWord, cyclicKindTwiceWeight]
  · have hSource : expandedSegmentWord blocks ≠ [] := by
      cases blocks with
      | nil => exact False.elim (hEmpty rfl)
      | cons block rest =>
          rcases block with ⟨middle, right⟩
          simp [expandedSegmentWord]
    have hLast : (expandedSegmentWord blocks).getLast? =
        some (kindLastOr .vertex (reducedSegmentWord blocks)) := by
      rw [getLast?_eq_kindLastOr_of_nonempty .vertex _ hSource,
        expandedSegmentWord_lastOr_eq_reduced]
    simp only [cyclicKindTwiceWeight, hLast]
    rw [← twiceExpandedSegmentBudget_eq_word]
    exact twice_segmentCount_le_expandedBudget blocks _ hNoMixed

namespace OrderOneData

universe v w
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The precise budget needed to use a size-`q` local forest on a reduced
cycle.  The literal cyclic segment decomposition and exclusion of mixed
singletons are required; order at most `q` alone is insufficient. -/
theorem BigCycle.segmentedReduct_length_le_cutoff
    {V' E' I' P' : Type w} {D' : OrderOneData V' E' I' P'}
    {n m q : ℕ} (C : D.BigCycle n) (B : D'.BigCycle m)
    (blocks : List CycleReductionBlock)
    (hSource : List.ofFn (fun i : Fin n =>
      connectorKind (C.connector i)) = expandedSegmentWord blocks)
    (hReduct : List.ofFn (fun j : Fin m =>
      connectorKind (B.connector j)) = reducedSegmentWord blocks)
    (hNoMixed : NoMixedSingletonSegments
      (kindLastOr .vertex (reducedSegmentWord blocks)) blocks)
    (hOrder : C.twiceOrder ≤ 2 * q) : m ≤ q := by
  have hLength : m = blocks.length := by
    simpa using congrArg List.length hReduct
  have hBudget := twice_segmentCount_le_cyclicExpandedWeight blocks hNoMixed
  have hSourceOrder : C.twiceOrder =
      cyclicKindTwiceWeight (expandedSegmentWord blocks) := by
    rw [C.twiceOrder_eq_cyclicKindList D, hSource]
  omega

/-- The forest-cycle conversion with its segment-count hypothesis actually
derived from the source order.  This concludes supremeness of the REDUCED
cycle; transferring it to the source still needs the physical cycle-transfer
theorem.  No reduced label is identified with a source designated label. -/
theorem BigCycle.segmentedReduct_hasSupreme_of_bottomLocalForest
    {V' E' I' P' : Type w} {D' : OrderOneData V' E' I' P'}
    {n m q : ℕ} (C : D.BigCycle n) (B : D'.BigCycle m)
    (H : D'.BottomForestGeometry) (hAccept : B.Acceptable)
    (hLocal : LocalForestThrough (D'.bottomForestPiece H) q)
    (blocks : List CycleReductionBlock)
    (hSource : List.ofFn (fun i : Fin n =>
      connectorKind (C.connector i)) = expandedSegmentWord blocks)
    (hReduct : List.ofFn (fun j : Fin m =>
      connectorKind (B.connector j)) = reducedSegmentWord blocks)
    (hNoMixed : NoMixedSingletonSegments
      (kindLastOr .vertex (reducedSegmentWord blocks)) blocks)
    (hOrder : C.twiceOrder ≤ 2 * q) : B.HasSimultaneousSupreme :=
  B.hasSimultaneousSupreme_of_bottomLocalForest D' H hAccept q hLocal
    (C.segmentedReduct_length_le_cutoff D B blocks hSource hReduct hNoMixed hOrder)

end OrderOneData
end StructuralRamsey.Girth

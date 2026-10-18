import Girth.TrainSegmentedCycleOrder

open StructuralRamsey.Girth

#print axioms StructuralRamsey.Girth.twiceReducedSegmentBudget_le_expanded
#print axioms StructuralRamsey.Girth.twiceReducedSegmentWord_le_expanded
#print axioms StructuralRamsey.Girth.cyclicReducedSegmentWord_le_expanded
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.reduct_twiceOrder_le_of_segmented_words
#print axioms StructuralRamsey.Girth.reducedSegmentWord_length_le_expanded
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.reduct_length_le_of_segmented_words

-- A nontrivial mixed vertex/wagon example with three segments.
example :
    twiceSegmentWeight CycleConnectorKind.wagon
      (reducedSegmentWord
        [([.vertex], .wagon), ([.wagon, .vertex], .vertex),
         ([], .wagon)]) ≤
      twiceSegmentWeight CycleConnectorKind.wagon
        (expandedSegmentWord
          [([.vertex], .wagon), ([.wagon, .vertex], .vertex),
           ([], .wagon)]) :=
  twiceReducedSegmentWord_le_expanded _ _

#print axioms StructuralRamsey.Girth.kindLastOr_append_segment
#print axioms StructuralRamsey.Girth.expandedSegmentWord_lastOr_eq_reduced
#print axioms StructuralRamsey.Girth.segmented_words_last_agree
#print axioms StructuralRamsey.Girth.cyclicReducedSegmentWord_le_expanded_of_nonempty
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.reduct_twiceOrder_le_of_nonempty_segmented_words

/-- The nonempty boundary theorem applies with several internal blocks,
including a segment with no internal connectors and the closing edge. -/
example :
    cyclicKindTwiceWeight
      (reducedSegmentWord
        [([.vertex], .wagon), ([.wagon, .vertex], .vertex),
         ([], .wagon)]) ≤
    cyclicKindTwiceWeight
      (expandedSegmentWord
        [([.vertex], .wagon), ([.wagon, .vertex], .vertex),
         ([], .wagon)]) := by
  apply cyclicReducedSegmentWord_le_expanded_of_nonempty
  decide

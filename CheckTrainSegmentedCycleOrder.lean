import Girth.TrainSegmentedCycleOrder

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

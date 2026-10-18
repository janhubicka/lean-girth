import Girth.TrainSegmentedCycleOrder

#print axioms StructuralRamsey.Girth.twiceReducedSegmentBudget_le_expanded
#print axioms StructuralRamsey.Girth.twiceReducedSegmentWord_le_expanded
#print axioms StructuralRamsey.Girth.cyclicReducedSegmentWord_le_expanded

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

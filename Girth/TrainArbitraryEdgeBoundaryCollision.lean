import Girth.TrainArbitraryPieceIncidence
import Girth.TrainShortReplacementNeighbour
import Girth.TrainFreshLongWagon
import Girth.TrainLongBoundaryCollision

/-!
# Circulation: a physical edge cannot occur on both sides of a boundary

A physical edge e at the end of one replacement block and at the
start of the next can arise in two ways on either side: it either
meets both original source connectors of that occurrence, or its
fresh parent wagon contains both original vertex boundaries.

If both sides are direct edge incidences, the one edge meets three
distinct source connector positions, impossible by source A2/A3.
Otherwise the edge's parent wagon is fresh and meets the same three
positions; the A3 two-contact window again forbids this.

This is the uniform collision principle needed for the remaining
adjacent-label check in arbitrary replacement-word legality.
No selected target or appendix input.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Either e directly meets both old boundaries of occurrence i, or
its fresh parent wagon contains the two old connector vertices. -/
def BigCycle.PhysicalEdgeBoundary
    {n : ℕ} (C : D.BigCycle n) (i : Fin n) (e : E) : Prop :=
  (D.Incident (.inr e) (C.connector (trainCyclicPred i)) ∧
   D.Incident (.inr e) (C.connector i)) ∨
  (C.InWagonAt (D.parent e) (trainCyclicPred i) ∧
   C.InWagonAt (D.parent e) i ∧
   ∀ t : Fin n, C.connector t ≠ Sum.inr (D.parent e))

/-- Three successive source positions cannot all contact a wagon
that was absent from the old connector list. -/
theorem BigCycle.fresh_wagon_not_three_successive
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (i : Fin n) (p : P)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hBefore : C.InWagonAt p (trainCyclicPred i))
    (hHere : C.InWagonAt p i)
    (hNext : C.InWagonAt p (cyclicSucc i)) : False := by
  have hHereNext :
      C.InWagonAt p (trainCyclicPred (cyclicSucc i)) := by
    simpa [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i]
      using hHere
  have hSame := C.nonconnector_wagon_boundary_occurrence_unique
    D hAccept hn p hFresh i (cyclicSucc i)
      hBefore hHere hHereNext hNext
  exact (C.ne_cyclicSucc D i) hSame

/-- A physical edge cannot be a compatible boundary label for
two consecutive source occurrence blocks, even if the two source
pieces have different designated owners. -/
theorem BigCycle.physical_edge_boundary_ne_next
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (i : Fin n) (e : E)
    (hLeft : C.PhysicalEdgeBoundary D i e)
    (hRight : C.PhysicalEdgeBoundary D (cyclicSucc i) e) : False := by
  rcases hLeft with hEdgeL | ⟨hWBefore, hWHere, hFreshL⟩
  · rcases hRight with hEdgeR | ⟨_hWNextBefore, hWNext, hFreshR⟩
    · have hPredNe : trainCyclicPred i ≠ i := by
        intro heq
        have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i
        rw [heq] at hs
        exact (C.ne_cyclicSucc D i) hs.symm
      exact C.not_edge_incident_three_distinct D hAccept e
        (trainCyclicPred i) i (cyclicSucc i)
        hPredNe (trainCyclicPred_ne_cyclicSucc_of_three_le hn i)
        (C.ne_cyclicSucc D i)
        hEdgeL.1 hEdgeL.2 hEdgeR.2
    · have hPrev : C.InWagonAt (D.parent e) (trainCyclicPred i) :=
        C.incident_edge_in_fresh_wagon_vertex
          D (D.parent e) hFreshR e rfl (trainCyclicPred i) hEdgeL.1
      have hHere : C.InWagonAt (D.parent e) i :=
        C.incident_edge_in_fresh_wagon_vertex
          D (D.parent e) hFreshR e rfl i hEdgeL.2
      exact C.fresh_wagon_not_three_successive D hAccept hn i
        (D.parent e) hFreshR hPrev hHere hWNext
  · rcases hRight with hEdgeR | ⟨_hWNextBefore, hWNext, _hFreshR⟩
    · have hNext : C.InWagonAt (D.parent e) (cyclicSucc i) :=
        C.incident_edge_in_fresh_wagon_vertex
          D (D.parent e) hFreshL e rfl (cyclicSucc i) hEdgeR.2
      exact C.fresh_wagon_not_three_successive D hAccept hn i
        (D.parent e) hFreshL hWBefore hWHere hNext
    · exact C.fresh_wagon_not_three_successive D hAccept hn i
        (D.parent e) hFreshL hWBefore hWHere hWNext

end StructuralRamsey.Girth.OrderOneData

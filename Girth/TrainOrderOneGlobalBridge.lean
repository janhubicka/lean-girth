import Girth.TrainTwoCopyIndexedSymmetry

/-!
# Circulation: globally legal indexed order-one bridges

In an order-one cycle A x B W the order-one bridge theorem supplies
an actual edge e in W through x for each designated label. A bridge
is a LOCAL short piece; the manuscript also requires the resulting
simultaneous replacement word to be a genuine big cycle.

For each designated side we retain that side and replace the other
side by the corresponding actual edge label. The new two-occurrence
cycle is constructed from the original vertex/wagon incidence data,
so we certify the GLOBAL replacement separately for either index.

These lemmas establish the length-two mixed-boundary base case of
Section 12. They do not prove the multi-segment order-one reduct.
No appendix definitions or proof are used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A designated label and an actual physical edge label are distinct,
even if they happen to have the same physical vertex carrier. -/
private theorem designated_ne_actual_edge
    (a : I ⊕ E) (e : E) (h : D.designated a) :
    a ≠ Sum.inr e := by
  cases a with
  | inl i => simp
  | inr f => simp [designated] at h

/-- Keep the FIRST designated label of an order-one vertex/wagon cycle,
using its bridge edge to replace the second occurrence. The resulting
two-label cyclic word has the same connectors and is globally legal. -/
theorem Cycle.first_indexed_global_of_bridge
    (C : D.Cycle) (hleft : D.designated C.left)
    (hBridge : D.Bridge C.left C.vertex C.wagon) :
    C.toBigCycle.HasSupremeAt D (0 : Fin 2) := by
  obtain ⟨e, he, hew, hxe⟩ := hBridge
  have hEdgeMeets : D.Meets (.inr e) C.wagon :=
    ⟨e, rfl, hew⟩
  have hEdgeVertex : D.Incident (.inr e) (.inl C.vertex) := by
    simpa [Incident, carrier] using hxe
  let B : D.Cycle := {
    left := C.left
    right := .inr e
    vertex := C.vertex
    wagon := C.wagon
    different := D.designated_ne_actual_edge C.left e hleft
    left_vertex := C.left_vertex
    right_vertex := by simpa [carrier] using hxe
    left_meets := C.left_meets
    right_meets := hEdgeMeets
    has_designated := Or.inl hleft
  }
  let pieces : Fin 2 → TrainSupremePiece E P := ![.keep, .short e]
  refine ⟨?_, pieces, ?_, ?_⟩
  · simpa [Cycle.toBigCycle] using hleft
  · intro k
    fin_cases k
    · constructor
      · intro _
        rfl
      · intro hne
        exact False.elim (hne rfl)
    · constructor
      · intro heq
        have hne : C.toBigCycle.label 1 ≠ C.toBigCycle.label 0 := by
          simpa [Cycle.toBigCycle] using C.different.symm
        exact False.elim (hne heq)
      · intro _
        simpa [pieces, BigCycle.ShortValid, Cycle.toBigCycle,
          trainCyclicPred] using
          (show e ∈ D.edges C.left ∧
            D.Incident (.inr e) (.inl C.vertex) ∧
            D.Incident (.inr e) (.inr C.wagon) from
            ⟨he, hEdgeVertex, hEdgeMeets⟩)
  · refine ⟨2, B.toBigCycle, ?_⟩
    simp [BigCycle.resultWord, BigCycle.pieceWord, pieces, B,
      Cycle.toBigCycle, List.ofFn, Fin.foldr_succ, Fin.foldr_zero]

/-- Keep the SECOND designated label of an order-one vertex/wagon
cycle and replace the first occurrence by its short bridge edge. -/
theorem Cycle.second_indexed_global_of_bridge
    (C : D.Cycle) (hright : D.designated C.right)
    (hBridge : D.Bridge C.right C.vertex C.wagon) :
    C.toBigCycle.HasSupremeAt D (1 : Fin 2) := by
  obtain ⟨e, he, hew, hxe⟩ := hBridge
  have hEdgeMeets : D.Meets (.inr e) C.wagon :=
    ⟨e, rfl, hew⟩
  have hEdgeVertex : D.Incident (.inr e) (.inl C.vertex) := by
    simpa [Incident, carrier] using hxe
  let B : D.Cycle := {
    left := .inr e
    right := C.right
    vertex := C.vertex
    wagon := C.wagon
    different := (D.designated_ne_actual_edge C.right e hright).symm
    left_vertex := by simpa [carrier] using hxe
    right_vertex := C.right_vertex
    left_meets := hEdgeMeets
    right_meets := C.right_meets
    has_designated := Or.inr hright
  }
  let pieces : Fin 2 → TrainSupremePiece E P := ![.short e, .keep]
  refine ⟨?_, pieces, ?_, ?_⟩
  · simpa [Cycle.toBigCycle] using hright
  · intro k
    fin_cases k
    · constructor
      · intro heq
        have hne : C.toBigCycle.label 0 ≠ C.toBigCycle.label 1 := by
          simpa [Cycle.toBigCycle] using C.different
        exact False.elim (hne heq)
      · intro _
        simpa [pieces, BigCycle.ShortValid, Cycle.toBigCycle,
          trainCyclicPred] using
          (show e ∈ D.edges C.right ∧
            D.Incident (.inr e) (.inr C.wagon) ∧
            D.Incident (.inr e) (.inl C.vertex) from
            ⟨he, hEdgeMeets, hEdgeVertex⟩)
    · constructor
      · intro _
        rfl
      · intro hne
        exact False.elim (hne rfl)
  · refine ⟨2, B.toBigCycle, ?_⟩
    simp [BigCycle.resultWord, BigCycle.pieceWord, pieces, B,
      Cycle.toBigCycle, List.ofFn, Fin.foldr_succ, Fin.foldr_zero]

/-- Both designated labels of an order-one mixed-boundary cycle
possess distinct indexed, globally legal short-collapse plans.
The order-one bridge bound supplies both actual bridge edges. -/
theorem Cycle.both_indexed_global_of_bound
    (h : D.Bound) (C : D.Cycle)
    (hleft : D.designated C.left)
    (hright : D.designated C.right) :
    C.toBigCycle.HasSupremeAt D (0 : Fin 2) ∧
    C.toBigCycle.HasSupremeAt D (1 : Fin 2) := by
  obtain ⟨hBridgeLeft, hBridgeRight⟩ :=
    D.both_bridges h C.left C.right C.vertex C.wagon
      C.different C.left_vertex C.right_vertex
      C.left_meets C.right_meets
  exact ⟨Cycle.first_indexed_global_of_bridge D C hleft hBridgeLeft,
    Cycle.second_indexed_global_of_bridge D C hright hBridgeRight⟩

end StructuralRamsey.Girth.OrderOneData

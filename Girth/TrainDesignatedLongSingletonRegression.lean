import Girth.TrainSimultaneousSupreme
import Mathlib.Tactic

/-!
# A3 does NOT rule out a designated singleton with a long piece

This finite ABSTRACT OrderOneData example has three designated
occurrences with vertex connectors x, y, z. The first designated
copy provides two distinct source edges in a common wagon through
x and y, and no edge joins x,y. Consequently the second occurrence
has a genuine LongValid piece from the first copy, although that
wagon is absent from the ORIGINAL connector word.

The source BigCycle satisfies A1, A2, and A3: the wagon in question
meets exactly the two CYCLICALLY ADJACENT vertex connector positions
x and y, which A3 explicitly permits.

This is a regression against the INVALID abstract shortcut
'long reduced piece => wagon already a connector'. It is not a
counterexample to a verified theorem or an assertion that this
particular abstract incidence data arises from an actual attached
picture. No appendix.
-/

namespace StructuralRamsey.Girth

/-- Three singleton physical edges; edges 0 and 1 have one common
wagon 0, while edge 2 lies in wagon 1. Each designated copy's
full carrier includes all three vertices. -/
def designatedLongSingletonData :
    OrderOneData (Fin 3) (Fin 3) (Fin 3) (Fin 2) where
  edgeCarrier e := {e}
  copyCarrier _ := Set.univ
  copyEdges _ := Set.univ
  parent e := if e = (2 : Fin 3) then 1 else 0

/-- Three different designated labels and three distinct vertex
connectors. Physical incidence is literal, not a carrier-label
identification. -/
def designatedLongSingletonCycle :
    (designatedLongSingletonData).BigCycle 3 where
  length_ge_two := by decide
  label := ![Sum.inl (0 : Fin 3), Sum.inl 1, Sum.inl 2]
  connector := ![Sum.inl (0 : Fin 3), Sum.inl 1, Sum.inl 2]
  adjacent_ne := by
    intro k
    fin_cases k <;> decide
  connector_injective := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all
  left_incident := by
    intro k
    fin_cases k <;> simp [OrderOneData.Incident, OrderOneData.carrier,
      designatedLongSingletonData]
  right_incident := by
    intro k
    fin_cases k
    · change (0 : Fin 3) ∈ (Set.univ : Set (Fin 3))
      exact Set.mem_univ _
    · change (1 : Fin 3) ∈ (Set.univ : Set (Fin 3))
      exact Set.mem_univ _
    · change (2 : Fin 3) ∈ (Set.univ : Set (Fin 3))
      exact Set.mem_univ _

/-- The abstract source cycle is acceptable; in particular A3
allows a nonconnector wagon touching two ADJACENT vertex positions. -/
theorem designatedLongSingletonCycle_acceptable :
    designatedLongSingletonCycle.Acceptable := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro _
    refine ⟨(0 : Fin 3), ?_⟩
    simp [OrderOneData.designated, designatedLongSingletonCycle]
  · constructor
    · intro j p hW _ _
      fin_cases j <;> simp [designatedLongSingletonCycle] at hW
    · intro j p x y hW _ _ _ _ _ _
      fin_cases j <;> simp [designatedLongSingletonCycle] at hW
  · intro p _hFresh
    fin_cases p
    · refine ⟨(0 : Fin 3), ?_⟩
      intro j hj
      fin_cases j
      · exact Or.inl rfl
      · exact Or.inr (by decide)
      · rcases hj with ⟨x, hx, edge, he, hxEdge⟩
        have hx2 : x = (2 : Fin 3) := by
          have hh : (2 : Fin 3) = x := by
            simpa [designatedLongSingletonCycle] using hx
          exact hh.symm
        subst x
        fin_cases edge <;>
          simp_all [designatedLongSingletonData, OrderOneData.parent,
            OrderOneData.edgeCarrier]
    · refine ⟨(1 : Fin 3), ?_⟩
      intro j hj
      fin_cases j
      · rcases hj with ⟨x, hx, edge, he, hxEdge⟩
        have hx0 : x = (0 : Fin 3) := by
          have hh : (0 : Fin 3) = x := by
            simpa [designatedLongSingletonCycle] using hx
          exact hh.symm
        subst x
        fin_cases edge <;>
          simp_all [designatedLongSingletonData, OrderOneData.parent,
            OrderOneData.edgeCarrier]
      · exact Or.inl rfl
      · exact Or.inr (by decide)

/-- Occurrence 1 has a genuine LONG replacement from designated
occurrence 0, using two different edges with the same parent wagon. -/
theorem designatedLongSingletonCycle_long_piece :
    designatedLongSingletonCycle.LongValid
      designatedLongSingletonData (0 : Fin 3) (1 : Fin 3)
      (0 : Fin 3) (0 : Fin 2) (1 : Fin 3) := by
  refine ⟨(0 : Fin 3), (1 : Fin 3), ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · simp [OrderOneData.edges, designatedLongSingletonData]
  · simp [OrderOneData.edges, designatedLongSingletonData]
  · decide
  · decide
  · decide
  · change (0 : Fin 3) ∈ (Set.univ : Set (Fin 3))
    exact Set.mem_univ _
  · change (1 : Fin 3) ∈ (Set.univ : Set (Fin 3))
    exact Set.mem_univ _
  · rintro ⟨edge, h0, h1⟩
    change (0 : Fin 3) = edge at h0
    change (1 : Fin 3) = edge at h1
    have hFalse : (0 : Fin 3) = 1 := h0.trans h1.symm
    exact (by decide : (0 : Fin 3) ≠ 1) hFalse

/-- The common wagon 0 of that genuine long piece is NOT among
the source cycle's connectors, all of which are vertices. -/
theorem designatedLongSingletonCycle_wagon_absent :
    ∀ k : Fin 3,
      designatedLongSingletonCycle.connector k ≠
        Sum.inr (0 : Fin 2) := by
  intro k
  fin_cases k <;> decide

end StructuralRamsey.Girth

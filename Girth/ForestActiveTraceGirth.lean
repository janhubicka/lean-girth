import Girth.ForestTraceAcyclic
import Girth.Berge
import Girth.ForestDistinctBoundaryAllowed

/-!
# Active girth from bounded forest completion: Track 2 candidate

The exact combinatorial reduction of the revised
`lem:puresubsystem`: for every bounded finite *indexed*
collection of active edges, a forest completion exists whose
members have empty, singleton or whole-edge active traces
and whose traces include each selected edge. A hypothetical
short Berge cycle gives such an indexed collection, and the
verified forest-union girth argument (through ForestTraceAcyclic)
rules it out.

This module does not assert the relational boundary trace
hypothesis or construct the forest completion; those are
separate actual-picture obligations. It has NOT been
compiled locally and is not a kernel certificate.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- The combinatorial part of active-subsystem girth. Every
finite indexed family of distinct active edges of cardinal
at most m has a forest completion with full-edge-or-singleton
traces. The conclusion is the absence of a Berge cycle of
length at most m in the active support. -/
theorem girthGT_of_bounded_trace_forest_completions
    (S : Set W) (H : Set (Set W)) (m : ℕ)
    (hLinear : LinearEdgeSet H)
    (hEdgeBig : ∀ e : Set W, e ∈ H → ¬ e.Subsingleton)
    (hComplete :
      ∀ (N : Type v) [Fintype N]
        (edge : N → Set W),
        Function.Injective edge →
        (∀ n : N, edge n ∈ H) →
        Fintype.card N ≤ m →
        ∃ (J : Type v), ∃ (finite : Fintype J),
          letI : Fintype J := finite
          ∃ F : J → HypergraphPiece W,
            ForestOfCopies F ∧
            (∀ j : J,
              ((F j).carrier ∩ S).Subsingleton ∨
              ∃ e : Set W, e ∈ H ∧ (F j).carrier ∩ S = e) ∧
            (∀ n : N, ∃ j : J,
              (F j).carrier ∩ S = edge n)) :
    GirthGT H m := by
  classical
  rintro ⟨c, hc⟩
  -- The forest-completion interface indexes families in Type v.
  -- A raw Fin c.length is Type 0, so use the actual finite edge set
  -- as a subtype of Set W : Type v. This also deduplicates physical edges.
  let N : Type v := {e : Set W // e ∈ Set.range c.edge}
  letI : Fintype N := (Set.finite_range c.edge).fintype
  let edge : N → Set W := Subtype.val
  have hEdgeInj : Function.Injective edge := Subtype.val_injective
  have hSurj :
      Function.Surjective
        (fun i : Fin c.length =>
          (⟨c.edge i, ⟨i, rfl⟩⟩ : N)) := by
    rintro ⟨e, he⟩
    obtain ⟨i, hi⟩ := he
    refine ⟨i, ?_⟩
    exact Subtype.ext hi
  have hCard : Fintype.card N ≤ m := by
    have hle : Fintype.card N ≤ Fintype.card (Fin c.length) :=
      Fintype.card_le_of_surjective
        (fun i : Fin c.length =>
          (⟨c.edge i, ⟨i, rfl⟩⟩ : N)) hSurj
    calc
      Fintype.card N ≤ Fintype.card (Fin c.length) := hle
      _ = c.length := by simp
      _ ≤ m := hc
  have hEdges : ∀ n : N, edge n ∈ H := by
    rintro ⟨e, ⟨i, hi⟩⟩
    change e ∈ H
    rw [← hi]
    exact c.edge_mem i
  obtain ⟨J, finite, F, hForest, hTrace, hEdgeTrace⟩ :=
    hComplete N edge hEdgeInj hEdges hCard
  letI : Fintype J := finite
  have hRangeSub : Set.range c.edge ⊆ H := by
    rintro e ⟨i, rfl⟩
    exact c.edge_mem i
  have hRangeTrace :
      ∀ e : Set W, e ∈ Set.range c.edge →
        ∃ j : J, (F j).carrier ∩ S = e := by
    intro e he
    exact hEdgeTrace ⟨e, he⟩
  have hRangeGirth : GirthGT (Set.range c.edge) m :=
    girthGT_selected_of_forest_edge_traces
      F hForest S H hLinear hEdgeBig hTrace
      (Set.range c.edge) hRangeSub hRangeTrace m
  let c' : BergeCycle (Set.range c.edge) :=
    c.ofEdgeMem (fun i => ⟨i, rfl⟩)
  exact hRangeGirth ⟨c', hc⟩

/-- Same girth conclusion when each completed member has the existing
`SmallOrWholeEdgeBoundary` property, including membership of the
whole trace edge in that member's own support. This interface is
suited to the checked active-boundary and mixed-owner modules. -/
theorem girthGT_of_bounded_smallOrWhole_forest_completions
    (S : Set W) (H : Set (Set W)) (m : ℕ)
    (hLinear : LinearEdgeSet H)
    (hEdgeBig : ∀ e : Set W, e ∈ H → ¬ e.Subsingleton)
    (hComplete :
      ∀ (N : Type v) [Fintype N]
        (edge : N → Set W),
        Function.Injective edge →
        (∀ n : N, edge n ∈ H) →
        Fintype.card N ≤ m →
        ∃ (J : Type v), ∃ (finite : Fintype J),
          letI : Fintype J := finite
          ∃ F : J → HypergraphPiece W,
            ForestOfCopies F ∧
            (∀ j : J, SmallOrWholeEdgeBoundary H S (F j)) ∧
            (∀ n : N, ∃ j : J,
              (F j).carrier ∩ S = edge n)) :
    GirthGT H m := by
  apply girthGT_of_bounded_trace_forest_completions
    S H m hLinear hEdgeBig
  intro N finite edge hInj hEdges hCard
  letI : Fintype N := finite
  obtain ⟨J, finite, F, hForest, hBoundary, hEdgeTrace⟩ :=
    hComplete N edge hInj hEdges hCard
  letI : Fintype J := finite
  refine ⟨J, finite, F, hForest, ?_, hEdgeTrace⟩
  intro j
  rcases hBoundary j with hSmall | ⟨e, he, _hOwn, hEq⟩
  · exact Or.inl hSmall
  · exact Or.inr ⟨e, he, hEq⟩

end StructuralRamsey.Girth

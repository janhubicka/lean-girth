import Girth.ForestTraceAcyclic
import Girth.Berge

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
  rintro ⟨c, hc⟩
  have hCard : Fintype.card (Fin c.length) ≤ m := by
    simpa using hc
  obtain ⟨J, finite, F, hForest, hTrace, hEdgeTrace⟩ :=
    hComplete (Fin c.length) c.edge c.edge_injective
      (fun n => c.edge_mem n) hCard
  letI : Fintype J := finite
  have hRangeSub : Set.range c.edge ⊆ H := by
    rintro e ⟨n, rfl⟩
    exact c.edge_mem n
  have hRangeTrace :
      ∀ e : Set W, e ∈ Set.range c.edge →
        ∃ j : J, (F j).carrier ∩ S = e := by
    rintro e ⟨n, rfl⟩
    exact hEdgeTrace n
  have hRangeGirth : GirthGT (Set.range c.edge) m :=
    girthGT_selected_of_forest_edge_traces
      F hForest S H hLinear hEdgeBig hTrace
      (Set.range c.edge) hRangeSub hRangeTrace m
  let c' : BergeCycle (Set.range c.edge) :=
    c.ofEdgeMem (fun i => ⟨i, rfl⟩)
  exact hRangeGirth ⟨c', hc⟩

end StructuralRamsey.Girth

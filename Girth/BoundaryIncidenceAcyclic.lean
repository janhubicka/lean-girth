import Girth.BoundaryIncidenceBerge
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # Girth makes the boundary incidence graph acyclic

Once incidence cycles have been converted to Berge cycles, the manuscript's
boundary contradiction becomes immediate: a cycle can use no more distinct
hyperedges than there are boundary-edge labels.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- A Berge cycle whose edges all come from a finite labelled family has
length at most the number of labels. -/
theorem BergeCycle.length_le_card_range
    [Fintype E]
    (edge : E → Set W)
    (c : BergeCycle (Set.range edge)) :
    c.length ≤ Fintype.card E := by
  classical
  have hLabel (i : Fin c.length) :
      ∃ e : E, edge e = c.edge i := by
    rcases c.edge_mem i with ⟨e, he⟩
    exact ⟨e, he⟩
  let label : Fin c.length → E :=
    fun i => Classical.choose (hLabel i)
  have hspec (i : Fin c.length) :
      edge (label i) = c.edge i :=
    Classical.choose_spec (hLabel i)
  have hinj : Function.Injective label := by
    intro i j hij
    apply c.edge_injective
    calc
      c.edge i = edge (label i) := (hspec i).symm
      _ = edge (label j) := congrArg edge hij
      _ = c.edge j := hspec j
  simpa using Fintype.card_le_of_injective label hinj

/-- If the labelled boundary family has at most g edges and Berge girth
strictly greater than g, then its bipartite incidence graph is acyclic. -/
theorem boundaryIncidenceGraph_isAcyclic_of_girthGT
    [Fintype E]
    (edge : E → Set W)
    (hEdgeInj : Function.Injective edge)
    (g : ℕ)
    (hcard : Fintype.card E ≤ g)
    (hgt : GirthGT (Set.range edge) g) :
    (boundaryIncidenceGraph edge).IsAcyclic := by
  intro z p hp
  let c : BergeCycle (Set.range edge) :=
    bergeCycleOfBoundaryIncidenceCycle edge hEdgeInj p hp
  apply hgt
  exact
    ⟨c, (BergeCycle.length_le_card_range edge c).trans hcard⟩

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- Pairwise-subsingleton labelled edges are enough to exclude incidence
cycles.  This is the form needed after restricting a forest of copies to one
part: labels need not be globally injective, but repeated labels can only carry
subsingleton sets and therefore cannot occur on a simple incidence cycle. -/
theorem boundaryIncidenceGraph_isAcyclic_of_pairwiseSubsingleton_of_girthGT
    [Fintype E]
    (edge : E → Set W)
    (hLinear :
      ∀ ⦃e f : E⦄, e ≠ f → (edge e ∩ edge f).Subsingleton)
    (g : ℕ)
    (hcard : Fintype.card E ≤ g)
    (hgt : GirthGT (Set.range edge) g) :
    (boundaryIncidenceGraph edge).IsAcyclic := by
  intro z p hp
  let c : BergeCycle (Set.range edge) :=
    bergeCycleOfBoundaryIncidenceCycle_of_pairwiseSubsingleton
      edge hLinear p hp
  apply hgt
  exact
    ⟨c, (BergeCycle.length_le_card_range edge c).trans hcard⟩

end StructuralRamsey.Girth

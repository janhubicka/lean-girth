import Girth.RestrictedForestGirth
import Girth.ForestIncidenceAcyclic
import Girth.Decoration

/-! # Forests restricted to one part of a transversal hypergraph

This specializes the abstract carrier-restriction theorem to the partite
situation used in the manuscript.  Transversality says that every ambient
support edge contains exactly one vertex in each part, so a common support
edge meets a fixed part in at most one vertex automatically.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι P : Type v}

/-- Exact form of the manuscript's "forests restricted to one part" observation:
if all support edges of the forest are edges of one transversal partite
hypergraph, then restricting every member to a fixed part yields a Berge-acyclic
carrier hypergraph. -/
theorem girthGT_forest_restricted_to_part
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι]
    {H : Set (Set W)} {part : W → P}
    (hForest : ForestOfCopies F)
    (hEdges :
      ∀ i : ι, ∀ ⦃e : Set W⦄, e ∈ (F i).edges → e ∈ H)
    (hTrans : EdgeTransversal H part)
    (p : P) (g : ℕ) :
    GirthGT
      (carrierEdgeFamily
        (fun i => (F i).restrictCarrier {x | part x = p})) g := by
  apply girthGT_restrictedCarrierEdgeFamily_of_forest
    hForest {x | part x = p}
  · intro i j hij e hei hej
    have heH : e ∈ H := hEdges i hei
    intro x hx y hy
    obtain ⟨w, hw, huniq⟩ := hTrans e heH p
    have hx' : x ∈ e ∧ part x = p := by
      exact ⟨hx.1, hx.2⟩
    have hy' : y ∈ e ∧ part y = p := by
      exact ⟨hy.1, hy.2⟩
    exact (huniq x hx').trans (huniq y hy').symm

end StructuralRamsey.Girth


namespace StructuralRamsey.Girth

universe v
variable {W ι P : Type v}

/-- Incidence-graph form of the manuscript's one-part forest observation.
The labels are the forest members themselves; no injectivity assumption on
their restricted carriers is required. -/
theorem boundaryIncidenceGraph_isAcyclic_of_forest_restricted_to_part
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι]
    {H : Set (Set W)} {part : W → P}
    (hForest : ForestOfCopies F)
    (hEdges :
      ∀ i : ι, ∀ ⦃e : Set W⦄, e ∈ (F i).edges → e ∈ H)
    (hTrans : EdgeTransversal H part)
    (p : P) :
    (boundaryIncidenceGraph
      (fun i =>
        ((F i).restrictCarrier {x | part x = p}).carrier)).IsAcyclic := by
  apply boundaryIncidenceGraph_isAcyclic_of_forest_restriction
    hForest {x | part x = p}
  intro i j hij e hei hej
  have heH : e ∈ H := hEdges i hei
  intro x hx y hy
  obtain ⟨w, hw, huniq⟩ := hTrans e heH p
  exact
    (huniq x ⟨hx.1, hx.2⟩).trans
      (huniq y ⟨hy.1, hy.2⟩).symm

end StructuralRamsey.Girth

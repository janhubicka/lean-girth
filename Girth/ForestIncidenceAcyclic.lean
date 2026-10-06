import Girth.BoundaryIncidenceAcyclic
import Girth.RestrictedForestGirth

/-! # Incidence acyclicity for restricted forests

The circulation proof compresses a Berge cycle through several standard
pictures to an alternating walk between local-copy labels and shared vertices
inside one part.  A local forest makes precisely this incidence graph acyclic.
This file packages that consequence directly, avoiding a separate
shortest-subwalk argument in later applications.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Restrict a finite forest to a vertex set that meets every common edge in
at most one vertex.  The labelled incidence graph of the restricted carriers
is acyclic. -/
theorem boundaryIncidenceGraph_isAcyclic_of_forest_restriction
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι]
    (hForest : ForestOfCopies F)
    (P : Set W)
    (hEdgePart :
      ∀ ⦃i j : ι⦄, i ≠ j → ∀ ⦃e : Set W⦄,
        e ∈ (F i).edges → e ∈ (F j).edges →
          (e ∩ P).Subsingleton) :
    (boundaryIncidenceGraph
      (fun i => ((F i).restrictCarrier P).carrier)).IsAcyclic := by
  let edge : ι → Set W :=
    fun i => ((F i).restrictCarrier P).carrier
  have hPair :
      ∀ ⦃i j : ι⦄, i ≠ j →
        (edge i ∩ edge j).Subsingleton := by
    simpa [edge] using
      pairwise_restrictedCarrier_subsingleton_of_allowed
        hForest.pairwiseAllowed P hEdgePart
  have hgt :
      GirthGT (Set.range edge) (Fintype.card ι) := by
    have h :=
      girthGT_restrictedCarrierEdgeFamily_of_forest
        hForest P hEdgePart (Fintype.card ι)
    simpa [edge, carrierEdgeFamily] using h
  exact
    boundaryIncidenceGraph_isAcyclic_of_pairwiseSubsingleton_of_girthGT
      edge hPair (Fintype.card ι) (by rfl) hgt

/-- One-part version: it is enough that every support edge of every forest
member meets the chosen part in at most one vertex. -/
theorem boundaryIncidenceGraph_isAcyclic_of_forest_part
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι]
    (hForest : ForestOfCopies F)
    (P : Set W)
    (hPart : EdgesMeetPartAtMostOne F P) :
    (boundaryIncidenceGraph
      (fun i => ((F i).restrictCarrier P).carrier)).IsAcyclic := by
  apply boundaryIncidenceGraph_isAcyclic_of_forest_restriction
    hForest P
  intro i j hij e hei hej
  exact hPart i hei


/-- Once the restricted-forest incidence graph is known to be acyclic, it has
no nonempty closed trail.  This is the exact endpoint needed after maximal
run compression in the circulation proof: the compressed alternating walk is
shown to be a circuit, with no further shortest-subwalk minimization. -/
theorem no_boundaryIncidenceCircuit_of_forest_restriction
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι]
    (hForest : ForestOfCopies F)
    (P : Set W)
    (hEdgePart :
      ∀ ⦃i j : ι⦄, i ≠ j → ∀ ⦃e : Set W⦄,
        e ∈ (F i).edges → e ∈ (F j).edges →
          (e ∩ P).Subsingleton)
    {z : ι ⊕ W}
    (p : (boundaryIncidenceGraph
      (fun i => ((F i).restrictCarrier P).carrier)).Walk z z) :
    ¬ p.IsCircuit := by
  intro hp
  have hAcyc :=
    boundaryIncidenceGraph_isAcyclic_of_forest_restriction
      hForest P hEdgePart
  exact hAcyc p.cycleBypass hp.isCycle_cycleBypass

end StructuralRamsey.Girth

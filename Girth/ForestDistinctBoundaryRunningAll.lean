import Girth.ForestDistinctBoundaryRunningCore

/-!
# Full running intersections in the temporary incidence family

The last geometric bridge for the all-distinct forest increment has
two independent cases for an ambient vertex x.

* If x is in the local core, selected members and temporary boundary
  nodes reach the unique vertex-node x by mandatory incidence links
  (ForestDistinctBoundaryRunningCore).
* If x is outside the local core, it belongs to at most one selected
  full-standard member, and no auxiliary edge or singleton piece
  contains it. Running intersections are then vacuous.

Consequently ANY actual tree on the augmented labels which retains
the mandatory boundary links is a join tree. Combining with the
already checked pairwise allowed intersections gives a forest of the
temporary augmented family. The only remaining construction is a
tree retaining those links, obtained by extending an acyclic
boundary-incidence skeleton. Auxiliary one-edge deletion is separate.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I E V : Type v}

/-- At any ambient vertex outside the local core, the augmented
incidence family has at most one member containing that vertex.
This statement requires neither acyclicity nor a join tree. -/
theorem augmentedBoundary_running_outside_core
    (selected : I → HypergraphPiece W)
    (S : Set W) (edge : E → Set W) (vertex : V → W)
    (hCross : ∀ ⦃i j : I⦄, i ≠ j →
      (selected i).carrier ∩ (selected j).carrier ⊆ S)
    (hEdgeSub : ∀ e : E, edge e ⊆ S)
    (hVertexSub : ∀ v : V, vertex v ∈ S)
    (G : SimpleGraph (I ⊕ (E ⊕ V)))
    (x : W) (hxOut : x ∉ S) :
    (G.induce {z | x ∈
      (augmentedBoundaryPieces selected edge vertex z).carrier}).Preconnected := by
  intro a b
  have hSelected :
      ∀ z : I ⊕ (E ⊕ V),
        x ∈ (augmentedBoundaryPieces selected edge vertex z).carrier →
        ∃ i : I, z = .inl i ∧ x ∈ (selected i).carrier := by
    intro z hz
    cases z with
    | inl i =>
        exact ⟨i, rfl, hz⟩
    | inr z =>
        cases z with
        | inl e =>
            change x ∈ edge e at hz
            exact (hxOut (hEdgeSub e hz)).elim
        | inr v =>
            change x ∈ ({vertex v} : Set W) at hz
            have hEq : x = vertex v := by simpa using hz
            have hxS : x ∈ S := by
              simpa [hEq] using hVertexSub v
            exact (hxOut hxS).elim
  obtain ⟨i, ha, hxi⟩ := hSelected a.1 a.2
  obtain ⟨j, hb, hxj⟩ := hSelected b.1 b.2
  have hij : i = j := by
    by_contra hne
    exact hxOut (hCross hne ⟨hxi, hxj⟩)
  have hab : a = b := by
    apply Subtype.ext
    calc
      a.1 = Sum.inl i := ha
      _ = Sum.inl j := congrArg Sum.inl hij
      _ = b.1 := hb.symm
  subst b
  exact SimpleGraph.Reachable.refl _

/-- Pairwise allowedness plus a TREE retaining all physical incidence
and selected-port links produces a genuine forest of the augmented
family. The remaining task is to construct such a tree from local
girth and the finite physical boundary labels. -/
theorem augmentedBoundary_forest_of_incidenceTree
    (selected : I → HypergraphPiece W)
    (S : Set W) (K : Set (Set W))
    (edge : E → Set W) (vertex : V → W)
    (port : I → Option (E ⊕ V))
    (G : SimpleGraph (I ⊕ (E ⊕ V)))
    (hTree : G.IsTree)
    (hLinear : LinearEdgeSet K)
    (hBoundary : ∀ i, SmallOrWholeEdgeBoundary K S (selected i))
    (hCross : ∀ ⦃i j : I⦄, i ≠ j →
      (selected i).carrier ∩ (selected j).carrier ⊆ S)
    (hEdge : ∀ e : E, edge e ∈ K)
    (hEdgeSub : ∀ e : E, edge e ⊆ S)
    (hVertexSub : ∀ v : V, vertex v ∈ S)
    (hPort : BoundaryPortExact selected S edge vertex port)
    (hAttach : ∀ i : I, ∀ z : E ⊕ V,
      port i = some z → G.Adj (.inl i) (.inr z))
    (hIncidence : ∀ e : E, ∀ v : V,
      vertex v ∈ edge e →
      G.Adj (.inr (.inl e)) (.inr (.inr v)))
    (hVertexInj : Function.Injective vertex)
    (hAllCoreVerticesRepresented :
      ∀ x : W, x ∈ S →
        (∃ z : I ⊕ (E ⊕ V),
          x ∈ (augmentedBoundaryPieces selected edge vertex z).carrier) →
        ∃ v : V, vertex v = x) :
    ForestOfCopies
      (augmentedBoundaryPieces selected edge vertex) := by
  let F := augmentedBoundaryPieces selected edge vertex
  have hPair : PairwiseAllowed F :=
    pairwiseAllowed_augmentedBoundaryPieces
      selected S K edge vertex hLinear
      hBoundary hCross hEdge hEdgeSub
  let J : JoinTree F := {
    tree := G
    isTree := hTree
    running := by
      intro x
      by_cases hxS : x ∈ S
      · exact augmentedBoundary_running_core_of_incidence_links
          selected S edge vertex port G
          hPort hAttach hIncidence hVertexInj
          hAllCoreVerticesRepresented x hxS
      · exact augmentedBoundary_running_outside_core
          selected S edge vertex hCross
          hEdgeSub hVertexSub G x hxS
  }
  exact ⟨hPair, Or.inr ⟨J⟩⟩

end StructuralRamsey.Girth

import Girth.ForestDistinctBoundaryAugmented

/-!
# Running intersections in the augmented boundary-incidence tree

At a local-core vertex x, the temporary vertex node labelled x is an
anchor for every augmented member containing x.

A selected piece connects to that anchor by one step if its boundary
is the singleton x, or by two steps through its whole boundary-edge
node. An auxiliary edge node connects directly to the vertex node;
the vertex node itself needs no step.

This statement is independent of graph acyclicity. It identifies the
EXACT mandatory adjacencies that any spanning incidence tree must
retain. The remaining graph construction must provide those edges
while retaining the tree property; outside-core running is handled
separately by distinct-owner disjointness.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I E V : Type v}

/-- Exact attachment of an original selected member to one boundary
node: empty, whole-edge, or singleton-vertex. Singleton and edge
labels refer to their true physical vertex sets. -/
def BoundaryPortExact
    (selected : I → HypergraphPiece W)
    (S : Set W)
    (edge : E → Set W)
    (vertex : V → W)
    (port : I → Option (E ⊕ V)) : Prop :=
  ∀ i : I,
    match port i with
    | none => (selected i).carrier ∩ S = ∅
    | some (.inl e) => (selected i).carrier ∩ S = edge e
    | some (.inr v) => (selected i).carrier ∩ S = {vertex v}

/-- Mandatory selected-leaf and physical edge-vertex incidences
already make each local-core occurrence set connected. There is no
claim that G is acyclic or connected on all labels. -/
theorem augmentedBoundary_running_core_of_incidence_links
    (selected : I → HypergraphPiece W)
    (S : Set W)
    (edge : E → Set W)
    (vertex : V → W)
    (port : I → Option (E ⊕ V))
    (G : SimpleGraph (I ⊕ (E ⊕ V)))
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
    ∀ x : W, x ∈ S →
      (G.induce {z | x ∈
        (augmentedBoundaryPieces selected edge vertex z).carrier}).Preconnected := by
  intro x hxS a b
  let occ : Set (I ⊕ (E ⊕ V)) :=
    {z | x ∈ (augmentedBoundaryPieces selected edge vertex z).carrier}
  obtain ⟨v, hv⟩ :=
    hAllCoreVerticesRepresented x hxS ⟨a.1, a.2⟩
  let root : occ := ⟨.inr (.inr v), by
    change x ∈ ({vertex v} : Set W)
    simp [hv]⟩
  have hReach (z : occ) :
      (G.induce occ).Reachable z root := by
    rcases z with ⟨z, hz⟩
    cases z with
    | inl i =>
        change x ∈ (selected i).carrier at hz
        have hxBoundary : x ∈ (selected i).carrier ∩ S :=
          ⟨hz, hxS⟩
        cases hp : port i with
        | none =>
            have hEmpty :
                (selected i).carrier ∩ S = ∅ := by
              simpa [BoundaryPortExact, hp] using hPort i
            rw [hEmpty] at hxBoundary
            exact False.elim (by simpa using hxBoundary)
        | some z =>
            cases z with
            | inl e =>
                have hBoundary :
                    (selected i).carrier ∩ S = edge e := by
                  simpa [BoundaryPortExact, hp] using hPort i
                have hxEdge : x ∈ edge e :=
                  hBoundary ▸ hxBoundary
                let mid : occ := ⟨.inr (.inl e), by
                  change x ∈ edge e
                  exact hxEdge⟩
                have hFirst :
                    (G.induce occ).Adj
                      (⟨.inl i, hz⟩ : occ) mid :=
                  hAttach i (.inl e) hp
                have hSecond :
                    (G.induce occ).Adj mid root :=
                  hIncidence e v (by simpa [hv] using hxEdge)
                exact hFirst.reachable.trans hSecond.reachable
            | inr u =>
                have hBoundary :
                    (selected i).carrier ∩ S = {vertex u} := by
                  simpa [BoundaryPortExact, hp] using hPort i
                have hVal : x = vertex u := by
                  have hh : x ∈ ({vertex u} : Set W) :=
                    hBoundary ▸ hxBoundary
                  simpa using hh
                have huv : u = v :=
                  hVertexInj (hVal.symm.trans hv.symm)
                subst u
                have hFirst :
                    (G.induce occ).Adj
                      (⟨.inl i, hz⟩ : occ) root :=
                  hAttach i (.inr v) hp
                exact hFirst.reachable
    | inr z =>
        cases z with
        | inl e =>
            change x ∈ edge e at hz
            have hLink :
                (G.induce occ).Adj
                  (⟨.inr (.inl e), hz⟩ : occ) root :=
              hIncidence e v (by simpa [hv] using hz)
            exact hLink.reachable
        | inr u =>
            change x ∈ ({vertex u} : Set W) at hz
            have hVal : x = vertex u := by simpa using hz
            have huv : u = v := hVertexInj (hVal.symm.trans hv.symm)
            subst u
            exact SimpleGraph.Reachable.refl _
  exact (hReach a).trans (hReach b).symm

end StructuralRamsey.Girth

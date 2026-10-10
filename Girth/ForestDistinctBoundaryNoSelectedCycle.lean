import Girth.ForestDistinctBoundarySkeleton
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Mandatory skeleton cycles cannot use selected labels

A selected label in the mandatory boundary-port skeleton has at most
one neighbour: its exact physical edge/vertex boundary port. A graph
cycle would require two different neighbours, so any cycle must live
entirely in the physical incidence subgraph.

This is the generic leaf-elimination half of the all-distinct forest
increment. The next step is to identify the physical induced subgraph
with the actual boundary-incidence graph and apply the girth bound.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I E V : Type v}

/-- Adding a selected label with at most one boundary port cannot
create a cycle. All possible cycles already occur among physical
edge and vertex nodes. -/
theorem boundaryPortSkeleton_isAcyclic_of_physicalInduced
    (edge : E → Set W) (vertex : V → W)
    (port : I → Option (E ⊕ V))
    (hPhysical :
      ((boundaryPortSkeleton edge vertex port).induce
        (Set.range (Sum.inr : E ⊕ V → I ⊕ (E ⊕ V)))).IsAcyclic) :
    (boundaryPortSkeleton edge vertex port).IsAcyclic := by
  classical
  let G := boundaryPortSkeleton edge vertex port
  let s : Set (I ⊕ (E ⊕ V)) :=
    Set.range (Sum.inr : E ⊕ V → I ⊕ (E ⊕ V))
  have hInduced : (G.induce s).IsAcyclic := hPhysical
  have hUnique : ∀ (i : I) (u : I ⊕ (E ⊕ V)),
      G.Adj (.inl i) u →
      ∃ z : E ⊕ V, port i = some z ∧ u = .inr z := by
    intro i u hu
    cases u with
    | inl j =>
        change False at hu
        exact hu.elim
    | inr z =>
        exact ⟨z, hu, rfl⟩
  intro a c hc
  have hNoSelected :
      ∀ i : I, (Sum.inl i : I ⊕ (E ⊕ V)) ∉ c.support := by
    intro i hi
    let d := c.rotate (Sum.inl i) hi
    have hd : d.IsCycle := hc.rotate hi
    have hnon : ¬d.Nil := hd.not_nil
    obtain ⟨z, hz, hsnd⟩ := hUnique i d.snd (d.adj_snd hnon)
    obtain ⟨t, ht, hpen⟩ :=
      hUnique i d.penultimate (d.adj_penultimate hnon).symm
    have hzt : z = t := Option.some.inj (hz.symm.trans ht)
    have heq : d.snd = d.penultimate :=
      hsnd.trans ((congrArg Sum.inr hzt).trans hpen.symm)
    exact hd.snd_ne_penultimate heq
  have hSupport : ∀ x ∈ c.support, x ∈ s := by
    intro x hx
    cases x with
    | inl i =>
        exact (hNoSelected i hx).elim
    | inr z =>
        exact ⟨z, rfl⟩
  let d := c.induce s hSupport
  have hMapped :
      (d.map (SimpleGraph.Embedding.induce s).toHom).IsCycle := by
    simpa [d] using hc
  have hd : d.IsCycle := SimpleGraph.Walk.IsCycle.of_map hMapped
  exact hInduced d hd

end StructuralRamsey.Girth

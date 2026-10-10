import Girth.ForestDistinctBoundaryNoSelectedCycle
import Girth.BoundaryIncidenceAcyclic

/-!
# Local girth excludes every mandatory boundary-port skeleton cycle

Each selected-copy label is a leaf (or isolated vertex); the physical
edge/vertex part of the skeleton is isomorphic to an induced subgraph
of the ordinary boundary incidence graph. The only assumptions for
that subgraph argument are injectivity of represented vertex labels
and acyclicity of the true physical incidence graph. Local girth > q
on at most q distinct physical boundary edges supplies acyclicity.

These are graph-theoretic kernels, independent of the existence of a
local Ramsey witness.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I E V : Type v}

/-- No cycle is created by the exact selected-copy ports when the
underlying physical boundary incidence graph is acyclic and vertex
labels represent pairwise distinct physical vertices. -/
theorem boundaryPortSkeleton_isAcyclic_of_incidenceAcyclic
    (edge : E → Set W) (vertex : V → W)
    (port : I → Option (E ⊕ V))
    (hVertexInj : Function.Injective vertex)
    (hIncidenceAcyclic : (boundaryIncidenceGraph edge).IsAcyclic) :
    (boundaryPortSkeleton edge vertex port).IsAcyclic := by
  classical
  let G := boundaryPortSkeleton edge vertex port
  let s : Set (I ⊕ (E ⊕ V)) :=
    Set.range (Sum.inr : E ⊕ V → I ⊕ (E ⊕ V))
  let label : s → E ⊕ V := fun z => Classical.choose z.2
  have hLabel (z : s) :
      (Sum.inr (label z) : I ⊕ (E ⊕ V)) = z.1 :=
    Classical.choose_spec z.2
  have hLabelInj : Function.Injective label := by
    intro a b hab
    apply Subtype.ext
    calc
      a.1 = Sum.inr (label a) := (hLabel a).symm
      _ = Sum.inr (label b) := congrArg Sum.inr hab
      _ = b.1 := hLabel b
  let physical : E ⊕ V → E ⊕ W := fun z =>
    match z with
    | .inl e => .inl e
    | .inr v => .inr (vertex v)
  have hPhysicalInj : Function.Injective physical := by
    intro a b hab
    cases a with
    | inl e =>
        cases b with
        | inl f =>
            have hef : e = f := by simpa [physical] using hab
            cases hef
            rfl
        | inr v =>
            simp [physical] at hab
    | inr v =>
        cases b with
        | inl e =>
            simp [physical] at hab
        | inr w =>
            have hvw : vertex v = vertex w := by
              simpa [physical] using hab
            cases hVertexInj hvw
            rfl
  let f : (G.induce s) →g (boundaryIncidenceGraph edge) :=
    { toFun := fun z => physical (label z)
      map_rel' := by
        intro a b hab
        have hab' :
            G.Adj (Sum.inr (label a)) (Sum.inr (label b)) := by
          rw [hLabel a, hLabel b]
          exact hab
        cases ha : label a <;> cases hb : label b <;>
          simpa [G, physical, boundaryPortSkeleton,
            boundaryIncidenceGraph, ha, hb] using hab' }
  have hMapInj : Function.Injective f := by
    intro a b hab
    change physical (label a) = physical (label b) at hab
    exact hLabelInj (hPhysicalInj hab)
  have hPhysicalInduced : (G.induce s).IsAcyclic :=
    SimpleGraph.IsAcyclic.comap f hMapInj hIncidenceAcyclic
  exact boundaryPortSkeleton_isAcyclic_of_physicalInduced
    edge vertex port hPhysicalInduced

/-- The full mandatory skeleton is acyclic when the distinct used
whole-support boundaries are actual local hyperedges and their count
does not exceed the local girth cutoff. -/
theorem boundaryPortSkeleton_isAcyclic_of_localGirth
    [Fintype E]
    (edge : E → Set W) (vertex : V → W)
    (port : I → Option (E ⊕ V))
    (K : Set (Set W)) (q : ℕ)
    (hEdgeInj : Function.Injective edge)
    (hVertexInj : Function.Injective vertex)
    (hCard : Fintype.card E ≤ q)
    (hEdge : ∀ e, edge e ∈ K)
    (hGirth : GirthGT K q) :
    (boundaryPortSkeleton edge vertex port).IsAcyclic := by
  have hSubset : Set.range edge ⊆ K := by
    rintro _ ⟨e, rfl⟩
    exact hEdge e
  have hUsedGirth : GirthGT (Set.range edge) q :=
    girthGT_of_subset hSubset hGirth
  have hIncidence :
      (boundaryIncidenceGraph edge).IsAcyclic :=
    boundaryIncidenceGraph_isAcyclic_of_girthGT
      edge hEdgeInj q hCard hUsedGirth
  exact boundaryPortSkeleton_isAcyclic_of_incidenceAcyclic
    edge vertex port hVertexInj hIncidence

end StructuralRamsey.Girth

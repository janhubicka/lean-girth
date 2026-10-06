import Girth.BoundaryIncidenceAcyclic
import Girth.RankedParentTree
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # Completing an acyclic incidence forest to a rooted tree

We restrict the boundary incidence graph to ambient vertices that actually
occur in some boundary edge.  Its components can then be connected by adding
only edge-node--edge-node edges.  Thus any spanning tree extending the
incidence forest introduces no new adjacency at an active vertex node.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- Ambient vertices that occur in at least one labelled boundary edge. -/
def BoundaryActiveVertex (edge : E → Set W) :=
  {x : W // ∃ e : E, x ∈ edge e}

/-- Restriction of one boundary edge to the active-vertex subtype. -/
def activeBoundaryEdge
    (edge : E → Set W) (e : E) :
    Set (BoundaryActiveVertex edge) :=
  {x | x.1 ∈ edge e}

/-- Inclusion of the active incidence graph into the original incidence
graph. -/
def activeBoundaryIncidenceHom
    (edge : E → Set W) :
    boundaryIncidenceGraph (activeBoundaryEdge edge) →g
      boundaryIncidenceGraph edge where
  toFun z :=
    match z with
    | .inl e => Sum.inl e
    | .inr x => Sum.inr x.1
  map_rel' := by
    intro a b hab
    cases a with
    | inl e =>
        cases b with
        | inl f =>
            simpa using hab
        | inr x =>
            change x.1 ∈ edge e
            simpa [activeBoundaryEdge] using hab
    | inr x =>
        cases b with
        | inl e =>
            change x.1 ∈ edge e
            simpa [activeBoundaryEdge] using hab
        | inr y =>
            simpa using hab

theorem activeBoundaryIncidenceHom_injective
    (edge : E → Set W) :
    Function.Injective (activeBoundaryIncidenceHom edge) := by
  intro a b h
  cases a with
  | inl e =>
      cases b with
      | inl f =>
          simpa [activeBoundaryIncidenceHom] using h
      | inr x =>
          simp [activeBoundaryIncidenceHom] at h
  | inr x =>
      cases b with
      | inl f =>
          simp [activeBoundaryIncidenceHom] at h
      | inr y =>
          have hval : x.1 = y.1 := by
            have hs :
                (Sum.inr x.1 : E ⊕ W) = Sum.inr y.1 := by
              simpa [activeBoundaryIncidenceHom] using h
            exact Sum.inr.inj hs
          have hxy : x = y := Subtype.ext hval
          simpa [hxy]

/-- Acyclicity passes to the active incidence graph. -/
theorem activeBoundaryIncidence_isAcyclic
    (edge : E → Set W)
    (hAcyc : (boundaryIncidenceGraph edge).IsAcyclic) :
    (boundaryIncidenceGraph (activeBoundaryEdge edge)).IsAcyclic :=
  SimpleGraph.IsAcyclic.comap
    (activeBoundaryIncidenceHom edge)
    (activeBoundaryIncidenceHom_injective edge)
    hAcyc

/-- Supergraph used to connect the active incidence forest: retain every
incidence edge and make the edge-node side complete, but add no vertex-node
adjacency. -/
def boundaryIncidenceCompletionGraph
    (edge : E → Set W) :
    SimpleGraph (E ⊕ BoundaryActiveVertex edge) where
  Adj a b :=
    match a, b with
    | .inl e, .inl f => e ≠ f
    | .inl e, .inr x => x.1 ∈ edge e
    | .inr x, .inl e => x.1 ∈ edge e
    | .inr _, .inr _ => False
  symm := ⟨by
    intro a b hab
    cases a with
    | inl e =>
        cases b with
        | inl f =>
            exact fun hfe => hab hfe.symm
        | inr x =>
            exact hab
    | inr x =>
        cases b with
        | inl e =>
            exact hab
        | inr y =>
            exact False.elim hab⟩
  loopless := ⟨by
    intro a
    cases a <;> simp⟩

@[simp]
theorem boundaryIncidenceCompletion_adj_left_left
    (edge : E → Set W) (e f : E) :
    (boundaryIncidenceCompletionGraph edge).Adj
      (Sum.inl e) (Sum.inl f) ↔ e ≠ f :=
  Iff.rfl

@[simp]
theorem boundaryIncidenceCompletion_adj_left_right
    (edge : E → Set W) (e : E)
    (x : BoundaryActiveVertex edge) :
    (boundaryIncidenceCompletionGraph edge).Adj
      (Sum.inl e) (Sum.inr x) ↔ x.1 ∈ edge e :=
  Iff.rfl

@[simp]
theorem boundaryIncidenceCompletion_adj_right_left
    (edge : E → Set W) (e : E)
    (x : BoundaryActiveVertex edge) :
    (boundaryIncidenceCompletionGraph edge).Adj
      (Sum.inr x) (Sum.inl e) ↔ x.1 ∈ edge e :=
  Iff.rfl

@[simp]
theorem boundaryIncidenceCompletion_not_adj_right_right
    (edge : E → Set W)
    (x y : BoundaryActiveVertex edge) :
    ¬(boundaryIncidenceCompletionGraph edge).Adj
      (Sum.inr x) (Sum.inr y) := by
  simp [boundaryIncidenceCompletionGraph]

/-- The active incidence graph is a subgraph of the completion graph. -/
theorem activeBoundaryIncidence_le_completion
    (edge : E → Set W) :
    boundaryIncidenceGraph (activeBoundaryEdge edge) ≤
      boundaryIncidenceCompletionGraph edge := by
  intro a b hab
  cases a with
  | inl e =>
      cases b with
      | inl f =>
          simpa using hab
      | inr x =>
          change x.1 ∈ edge e
          simpa [activeBoundaryEdge] using hab
  | inr x =>
      cases b with
      | inl e =>
          change x.1 ∈ edge e
          simpa [activeBoundaryEdge] using hab
      | inr y =>
          simpa using hab

/-- Every node in the completion graph reaches a fixed edge-node. -/
theorem boundaryIncidenceCompletion_reachable_root
    [Nonempty E]
    (edge : E → Set W)
    (root : E)
    (z : E ⊕ BoundaryActiveVertex edge) :
    (boundaryIncidenceCompletionGraph edge).Reachable
      z (Sum.inl root) := by
  classical
  cases z with
  | inl e =>
      by_cases h : e = root
      · subst e
        exact SimpleGraph.Reachable.refl _
      · exact
          (show (boundaryIncidenceCompletionGraph edge).Adj
              (Sum.inl e) (Sum.inl root) by
            simpa using h).reachable
  | inr x =>
      rcases x.2 with ⟨e, hxe⟩
      have hxedge :
          (boundaryIncidenceCompletionGraph edge).Adj
            (Sum.inr x) (Sum.inl e) := by
        exact hxe
      by_cases h : e = root
      · subst e
        exact hxedge.reachable
      · have heroot :
            (boundaryIncidenceCompletionGraph edge).Adj
              (Sum.inl e) (Sum.inl root) := by
          simpa using h
        exact hxedge.reachable.trans heroot.reachable

/-- The completion graph is connected as soon as there is one edge label. -/
theorem boundaryIncidenceCompletion_connected
    [Nonempty E]
    (edge : E → Set W) :
    (boundaryIncidenceCompletionGraph edge).Connected := by
  let root : E := Classical.choice (inferInstance : Nonempty E)
  refine ⟨?_⟩
  intro a b
  exact
    (boundaryIncidenceCompletion_reachable_root
      edge root a).trans
      (boundaryIncidenceCompletion_reachable_root
        edge root b).symm

/-- An acyclic incidence forest extends to a tree by adding only
edge-node--edge-node links. -/
theorem exists_boundaryIncidenceCompletionTree
    [Nonempty E]
    (edge : E → Set W)
    (hAcyc : (boundaryIncidenceGraph edge).IsAcyclic) :
    ∃ T : SimpleGraph (E ⊕ BoundaryActiveVertex edge),
      boundaryIncidenceGraph (activeBoundaryEdge edge) ≤ T ∧
      T ≤ boundaryIncidenceCompletionGraph edge ∧
      T.IsTree := by
  have hActive :
      (boundaryIncidenceGraph (activeBoundaryEdge edge)).IsAcyclic :=
    activeBoundaryIncidence_isAcyclic edge hAcyc
  exact
    (boundaryIncidenceCompletion_connected edge).exists_isTree_le_of_le_of_isAcyclic
      (activeBoundaryIncidence_le_completion edge)
      hActive

end StructuralRamsey.Girth

import Girth.ForestCompletionSeparatorRequests
import Girth.Forest

/-!
# Allowed intersections across a join-tree edge

The leaf step of the manuscript's join-tree lifting proof needs a
short local assertion. If the cross-family overlap lies inside a
common support edge e, and each member has an allowed intersection
with its local request e^+, then the cross-family intersection is
allowed. In the nonsubsingleton case it is exactly e, which
belongs to the own support of BOTH members.

No ambient linearity premise is needed at this final step: that
premise has already been used to identify the outer separator
with the physical edge e. This module does not assert the full
finite join-tree lifting theorem.

Candidate source; Lean compilation and axiom audit are pending.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- A one-edge piece has an allowed intersection with itself. -/
theorem allowedIntersection_oneEdge_self (e : Set W) :
    AllowedIntersection
      (HypergraphPiece.oneEdge e) (HypergraphPiece.oneEdge e) := by
  right
  refine ⟨e, ?_, ?_, ?_⟩
  · simp [HypergraphPiece.oneEdge]
  · simp [HypergraphPiece.oneEdge]
  · simp [HypergraphPiece.oneEdge]

/-- A piece which meets a requested one-edge piece in at least two
vertices must contain the entire requested edge in its own support.
This is stronger than mere carrier containment. -/
theorem ownEdge_of_allowed_oneEdge_large
    (F : HypergraphPiece W) (e : Set W)
    (hAllowed : AllowedIntersection F (HypergraphPiece.oneEdge e))
    (hLarge : ¬(F.carrier ∩ e).Subsingleton) :
    e ∈ F.edges := by
  rcases hAllowed with hSmall | ⟨f, hf, hOne, _⟩
  · exact (hLarge hSmall).elim
  · have hEq : f = e := by
      simpa [HypergraphPiece.oneEdge] using hOne
    simpa [hEq] using hf

/-- The request e^+ at a local owner is allowed to meet every
member, including itself; only different labels use pairwiseAllowed. -/
theorem allowedIntersection_with_local_request
    {F : I → HypergraphPiece W}
    (hAllowed : PairwiseAllowed F)
    (connector : I) (e : Set W)
    (hRequest : F connector = HypergraphPiece.oneEdge e) :
    ∀ i : I, AllowedIntersection (F i) (HypergraphPiece.oneEdge e) := by
  intro i
  by_cases h : i = connector
  · subst i
    rw [hRequest]
    exact allowedIntersection_oneEdge_self e
  · rw [← hRequest]
    exact hAllowed h

/-- The cross-family lemma: a large cross intersection confined to
an outer separator e forces e into BOTH own edge sets, hence the
full cross intersection is precisely e. The small case is immediate. -/
theorem allowedIntersection_cross_of_common_request
    (F G : HypergraphPiece W) (e : Set W)
    (hCross : F.carrier ∩ G.carrier ⊆ e)
    (hF : AllowedIntersection F (HypergraphPiece.oneEdge e))
    (hG : AllowedIntersection G (HypergraphPiece.oneEdge e)) :
    AllowedIntersection F G := by
  by_cases hSmall :
      (F.carrier ∩ G.carrier).Subsingleton
  · exact Or.inl hSmall
  · have hFLarge : ¬(F.carrier ∩ e).Subsingleton := by
      intro hs
      apply hSmall
      intro x hx y hy
      exact hs ⟨hx.1, hCross hx⟩ ⟨hy.1, hCross hy⟩
    have hGLarge : ¬(G.carrier ∩ e).Subsingleton := by
      intro hs
      apply hSmall
      intro x hx y hy
      exact hs ⟨hx.2, hCross hx⟩ ⟨hy.2, hCross hy⟩
    have heF : e ∈ F.edges :=
      ownEdge_of_allowed_oneEdge_large F e hF hFLarge
    have heG : e ∈ G.edges :=
      ownEdge_of_allowed_oneEdge_large G e hG hGLarge
    have hEq : F.carrier ∩ G.carrier = e := by
      apply Set.Subset.antisymm hCross
      intro x hx
      exact ⟨F.edge_subset heF hx, G.edge_subset heG hx⟩
    exact Or.inr ⟨e, heF, heG, hEq⟩

end StructuralRamsey.Girth

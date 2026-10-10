import Girth.ForestDistinctBoundaryAllowed
import Girth.ForestCompletionSeparatorRequests

/-!
# Auxiliary incidence pieces in the distinct-owner forest increment

The join-tree construction temporarily adjoins one-edge pieces for
actual distinct boundary edges, and *formal* singleton one-edge
pieces for represented boundary vertices. These singleton edges are
NOT asserted to be support edges of the actual local hypergraph:
they are bookkeeping devices removed by ForestOfCopies.erase_oneEdge.

Pairwise allowed intersections with each temporary piece are simple
consequences of the whole-edge-or-singleton boundary criterion and
linearity. This module isolates them, so the remaining incidence
join-tree construction can work with a family already known to have
allowed intersections.

It does NOT assert that the augmented family is already a forest.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- A selected full-standard member meets an auxiliary local edge
in at most one vertex, unless that edge is exactly its own whole
boundary and hence belongs to its true support hypergraph. -/
theorem allowedIntersection_selected_boundaryEdge
    (F : HypergraphPiece W)
    (S : Set W) (K : Set (Set W))
    (hLinear : LinearEdgeSet K)
    (hBoundary : SmallOrWholeEdgeBoundary K S F)
    (e : Set W) (heK : e ∈ K) (heS : e ⊆ S) :
    AllowedIntersection F (HypergraphPiece.oneEdge e) := by
  change (F.carrier ∩ e).Subsingleton ∨
    ∃ f : Set W, f ∈ F.edges ∧ f ∈ ({e} : Set (Set W)) ∧
      F.carrier ∩ e = f
  rcases hBoundary with hSmall | ⟨f, hfK, hfF, hfBoundary⟩
  · left
    intro x hx y hy
    exact hSmall ⟨hx.1, heS hx.2⟩ ⟨hy.1, heS hy.2⟩
  · by_cases hOne : (F.carrier ∩ e).Subsingleton
    · exact Or.inl hOne
    · obtain ⟨x, hx, y, hy, hxy⟩ :=
        Set.not_subsingleton_iff.mp hOne
      have hxF : x ∈ f := by
        rw [← hfBoundary]
        exact ⟨hx.1, heS hx.2⟩
      have hyF : y ∈ f := by
        rw [← hfBoundary]
        exact ⟨hy.1, heS hy.2⟩
      have hSame : f = e := by
        by_contra hne
        have hSub : (f ∩ e).Subsingleton :=
          hLinear hfK heK hne
        exact hxy (hSub ⟨hxF, hx.2⟩ ⟨hyF, hy.2⟩)
      subst f
      right
      refine ⟨e, hfF, by simp, ?_⟩
      apply Set.Subset.antisymm
      · exact Set.inter_subset_right
      · intro z hz
        exact ⟨F.edge_subset hfF hz, hz⟩

/-- A purely formal singleton auxiliary piece has allowed intersection
with every original selected member. -/
theorem allowedIntersection_selected_boundaryVertex
    (F : HypergraphPiece W) (x : W) :
    AllowedIntersection F (HypergraphPiece.oneEdge ({x} : Set W)) := by
  left
  intro a ha b hb
  have ha' : a = x := by simpa using ha.2
  have hb' : b = x := by simpa using hb.2
  exact ha'.trans hb'.symm

/-- Two auxiliary edge pieces have allowed intersection in a linear
local support hypergraph, even before duplicate physical edges
have been removed from the labels. -/
theorem allowedIntersection_boundaryEdges
    (K : Set (Set W)) (hLinear : LinearEdgeSet K)
    {e f : Set W} (he : e ∈ K) (hf : f ∈ K) :
    AllowedIntersection (HypergraphPiece.oneEdge e)
      (HypergraphPiece.oneEdge f) := by
  by_cases heq : e = f
  · subst f
    right
    refine ⟨e, by simp [HypergraphPiece.oneEdge],
      by simp [HypergraphPiece.oneEdge], ?_⟩
    simp [HypergraphPiece.oneEdge]
  · left
    exact hLinear he hf heq

/-- All intersections involving a formal singleton auxiliary piece
are subsingletons, irrespective of other support edges. -/
theorem allowedIntersection_boundaryVertex_any
    (F : HypergraphPiece W) (x : W) :
    AllowedIntersection (HypergraphPiece.oneEdge ({x} : Set W)) F :=
  allowedIntersection_symm
    (allowedIntersection_selected_boundaryVertex F x)

end StructuralRamsey.Girth

import Girth.ForestDistinctBoundaryAuxiliary

/-!
# Pairwise-allowedness of the whole temporary incidence family

The direct forest increment uses a labelled incidence forest with three
sorts of nodes:

* the genuinely selected A/B support pieces;
* distinct local boundary support-edge nodes;
* boundary vertex nodes (represented by purely formal singleton pieces).

Pairwise intersections of EVERY two nodes of this family are allowed.
This packages the already formalized cases in one property on a
single disjoint-sum index type.

The open geometric task is to supply a join tree on the augmented
family, using the acyclic incidence graph and the actual boundary
attachment maps, then delete the temporary one-edge nodes. The
pairwise theorem here does not assert join-tree existence.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I E V : Type v}

/-- Actual selected pieces together with one-edge boundary pieces
and formal one-edge singleton boundary vertices. The labels of these
three kinds remain distinct even when their carriers coincide. -/
def augmentedBoundaryPieces
    (selected : I → HypergraphPiece W)
    (edge : E → Set W)
    (vertex : V → W) :
    I ⊕ (E ⊕ V) → HypergraphPiece W
  | .inl i => selected i
  | .inr (.inl e) => HypergraphPiece.oneEdge (edge e)
  | .inr (.inr v) => HypergraphPiece.oneEdge ({vertex v} : Set W)

/-- All pairwise intersections in the augmented incidence family
are allowed, under EXACTLY the distinct-owner boundary geometry
of the direct forest increment and linearity of the core edges. -/
theorem pairwiseAllowed_augmentedBoundaryPieces
    (selected : I → HypergraphPiece W)
    (S : Set W) (K : Set (Set W))
    (edge : E → Set W) (vertex : V → W)
    (hLinear : LinearEdgeSet K)
    (hBoundary :
      ∀ i, SmallOrWholeEdgeBoundary K S (selected i))
    (hCross : ∀ ⦃i j : I⦄, i ≠ j →
       (selected i).carrier ∩ (selected j).carrier ⊆ S)
    (hEdge : ∀ e : E, edge e ∈ K)
    (hEdgeSub : ∀ e : E, edge e ⊆ S) :
    PairwiseAllowed
      (augmentedBoundaryPieces selected edge vertex) := by
  have hSelected : PairwiseAllowed selected :=
    pairwiseAllowed_of_distinctOwner_boundaries
      selected S K hLinear hBoundary hCross
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      change AllowedIntersection (selected i) (selected j)
      exact hSelected (by
        intro hij
        exact hab (congrArg Sum.inl hij))
    | inr bj =>
      cases bj with
      | inl e =>
        change AllowedIntersection (selected i)
          (HypergraphPiece.oneEdge (edge e))
        exact allowedIntersection_selected_boundaryEdge
          (selected i) S K hLinear (hBoundary i)
          (edge e) (hEdge e) (hEdgeSub e)
      | inr x =>
        change AllowedIntersection (selected i)
          (HypergraphPiece.oneEdge ({vertex x} : Set W))
        exact allowedIntersection_selected_boundaryVertex
          (selected i) (vertex x)
  | inr ai =>
    cases ai with
    | inl e =>
      cases b with
      | inl j =>
        change AllowedIntersection
          (HypergraphPiece.oneEdge (edge e)) (selected j)
        exact allowedIntersection_symm
          (allowedIntersection_selected_boundaryEdge
            (selected j) S K hLinear (hBoundary j)
            (edge e) (hEdge e) (hEdgeSub e))
      | inr bj =>
        cases bj with
        | inl f =>
          change AllowedIntersection
            (HypergraphPiece.oneEdge (edge e))
            (HypergraphPiece.oneEdge (edge f))
          exact allowedIntersection_boundaryEdges
            K hLinear (hEdge e) (hEdge f)
        | inr x =>
          change AllowedIntersection
            (HypergraphPiece.oneEdge (edge e))
            (HypergraphPiece.oneEdge ({vertex x} : Set W))
          exact allowedIntersection_selected_boundaryVertex
            (HypergraphPiece.oneEdge (edge e)) (vertex x)
    | inr x =>
      cases b with
      | inl j =>
        change AllowedIntersection
          (HypergraphPiece.oneEdge ({vertex x} : Set W))
          (selected j)
        exact allowedIntersection_boundaryVertex_any
          (selected j) (vertex x)
      | inr bj =>
        cases bj with
        | inl f =>
          change AllowedIntersection
            (HypergraphPiece.oneEdge ({vertex x} : Set W))
            (HypergraphPiece.oneEdge (edge f))
          exact allowedIntersection_boundaryVertex_any
            (HypergraphPiece.oneEdge (edge f)) (vertex x)
        | inr y =>
          change AllowedIntersection
            (HypergraphPiece.oneEdge ({vertex x} : Set W))
            (HypergraphPiece.oneEdge ({vertex y} : Set W))
          exact allowedIntersection_boundaryVertex_any
            (HypergraphPiece.oneEdge ({vertex y} : Set W))
            (vertex x)

end StructuralRamsey.Girth

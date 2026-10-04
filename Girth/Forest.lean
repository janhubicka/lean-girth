import Girth.TreeSupport
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # Forests of copies and join trees

This module formalizes Definition 4.1 of the girth manuscript.  We use a
labelled finite family of hypergraph pieces.  A join tree is an ordinary
`SimpleGraph.IsTree` on the labels, and the running-intersection property says
that for every ambient vertex the induced graph on the pieces containing that
vertex is preconnected.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- A hypergraph piece remembers its vertex carrier and the support edges
belonging to the piece. -/
structure HypergraphPiece (W : Type v) where
  carrier : Set W
  edges : Set (Set W)
  edge_subset_carrier : ∀ ⦃e⦄, e ∈ edges → e ⊆ carrier

namespace HypergraphPiece

/-- An edge of a piece is in particular contained in its carrier. -/
theorem edge_subset (F : HypergraphPiece W) {e : Set W} (he : e ∈ F.edges) :
    e ⊆ F.carrier :=
  F.edge_subset_carrier he

end HypergraphPiece

/-- The pairwise intersection condition in Definition 4.1: two different
members meet in at most one vertex, or their whole carrier intersection is a
support edge belonging to both pieces. -/
def AllowedIntersection (F G : HypergraphPiece W) : Prop :=
  (F.carrier ∩ G.carrier).Subsingleton ∨
    ∃ e : Set W, e ∈ F.edges ∧ e ∈ G.edges ∧
      F.carrier ∩ G.carrier = e

theorem allowedIntersection_symm {F G : HypergraphPiece W}
    (h : AllowedIntersection F G) :
    AllowedIntersection G F := by
  rcases h with hs | ⟨e, hF, hG, he⟩
  · left
    simpa [Set.inter_comm] using hs
  · right
    exact ⟨e, hG, hF, by simpa [Set.inter_comm] using he⟩

/-- Pairwise allowed intersections for a labelled family. -/
def PairwiseAllowed (F : ι → HypergraphPiece W) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → AllowedIntersection (F i) (F j)

/-- A join tree for a family of pieces.  The induced subtree on all members
containing a fixed ambient vertex is preconnected; this is exactly the
running-intersection condition. -/
structure JoinTree (F : ι → HypergraphPiece W) where
  tree : SimpleGraph ι
  isTree : tree.IsTree
  running : ∀ x : W,
    (tree.induce {i : ι | x ∈ (F i).carrier}).Preconnected

namespace JoinTree

/-- The running-intersection condition gives reachability inside the induced
occurrence graph of every ambient vertex. -/
theorem occurrence_reachable
    {F : ι → HypergraphPiece W} (J : JoinTree F)
    (x : W)
    (i j : {k : ι | x ∈ (F k).carrier}) :
    (J.tree.induce {k : ι | x ∈ (F k).carrier}).Reachable i j :=
  J.running x i j

end JoinTree

/-- A finite labelled family is a forest of copies when its pair intersections
are allowed and either the family is empty or it admits a join tree.  This
explicitly includes the manuscript's empty-family convention. -/
def ForestOfCopies (F : ι → HypergraphPiece W) : Prop :=
  PairwiseAllowed F ∧
    (IsEmpty ι ∨ Nonempty (JoinTree F))

theorem ForestOfCopies.pairwiseAllowed
    {F : ι → HypergraphPiece W} (h : ForestOfCopies F) :
    PairwiseAllowed F :=
  h.1

theorem ForestOfCopies.joinTree_of_nonempty
    {F : ι → HypergraphPiece W} [Nonempty ι]
    (h : ForestOfCopies F) :
    Nonempty (JoinTree F) := by
  rcases h.2 with hEmpty | hJ
  · exact (not_isEmpty_of_nonempty ι hEmpty).elim
  · exact hJ

end StructuralRamsey.Girth

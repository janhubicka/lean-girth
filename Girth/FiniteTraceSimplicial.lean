import Girth.FiniteTracePairGraph
import Girth.ForestEnumeration

/-!
# Private leaf vertices are simplicial in the trace pair graph

The source of chordality for a running-intersection family is elementary.
If x occurs in a leaf bag but not its unique neighbouring bag, running
intersection implies x occurs in no other bag.  All neighbours of x
in the pair graph consequently lie in the leaf bag and are pairwise
adjacent.  Such vertices may be eliminated without creating chords.

These statements are the precise local geometric step towards the
remaining chordality theorem.  The global chordal elimination and
maximal-clique join-tree theorem are NOT claimed here.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- A vertex private to a leaf relative to its unique neighbour
occurs in that leaf and nowhere else in the join-tree family. -/
theorem JoinTree.private_leaf_occurs_only
    {F : ι → HypergraphPiece W}
    (J : JoinTree F)
    {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent)
    {x : W}
    (hxLeaf : x ∈ (F leaf).carrier)
    (hxNotParent : x ∉ (F parent).carrier) :
    ∀ j : ι, x ∈ (F j).carrier → j = leaf := by
  intro j hxj
  by_contra hne
  exact hxNotParent
    (J.mem_parent_of_mem_leaf_and_other
      hadj huniq hne hxLeaf hxj)

/-- A private leaf vertex is simplicial in the pair graph on Z:
any two distinct neighbours of it are adjacent to each other.
The join tree is for the ORIGINAL bags; no outside bags occur. -/
theorem tracePairGraph_private_leaf_simplicial
    (F : ι → Set W) (Z : Set W)
    (J : JoinTree (fun i => setBagPiece (F i)))
    {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent)
    (x : Z)
    (hxLeaf : x.1 ∈ F leaf)
    (hxNotParent : x.1 ∉ F parent) :
    ∀ y z : Z, y ≠ z →
      (tracePairGraph F Z).Adj x y →
      (tracePairGraph F Z).Adj x z →
      (tracePairGraph F Z).Adj y z := by
  have hxOnly :
      ∀ j : ι, x.1 ∈ F j → j = leaf :=
    J.private_leaf_occurs_only hadj huniq hxLeaf hxNotParent
  intro y z hyz hxy hxz
  obtain ⟨_, i, hxi, hyi⟩ := hxy
  obtain ⟨_, j, hxj, hzj⟩ := hxz
  have hi : i = leaf := hxOnly i hxi
  have hj : j = leaf := hxOnly j hxj
  subst i
  subst j
  exact ⟨hyz, leaf, hyi, hzj⟩

end StructuralRamsey.Girth

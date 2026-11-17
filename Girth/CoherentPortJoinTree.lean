import Girth.ForestJoinGlue

/-!
# A coherent single-port interface for gluing join trees

This is a conservative abstraction of the binary join-tree glue used by the
circulation proof. The interface can be an arbitrary vertex set, including
a union of several support edges; no linearity or edge assumption is hidden
in the definition.

There are TWO independent requirements:
* all cross-side vertices belong to the interface, and one chosen local
  member on each side covers that interface (a one-node coherent port);
* if a *forest of copies* rather than just a join tree is wanted, every
  cross-side pair of members must have an allowed full intersection.

The first requirement is sufficient for the running-intersection invariant.
It is not sufficient for AllowedIntersection, closure, or preservation of
unselected coloured A-copies.

A connected marked *subtree* of helpers, rather than a single helper on
each side, requires a new gluing theorem and is not proved here.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W I J : Type v}

/-- Data for a single-node coherent interface between two local families.
Every cross-side overlap is inside the same port, and the two connector
members represent every vertex of the port. -/
structure BridgeData
    (F : I → HypergraphPiece W) (G : J → HypergraphPiece W)
    (i₀ : I) (j₀ : J) where
  port : Set W
  left_cover : port ⊆ (F i₀).carrier
  right_cover : port ⊆ (G j₀).carrier
  cross_inside : ∀ i j, (F i).carrier ∩ (G j).carrier ⊆ port

/-- The one-port record supplies the exact cross-occurrence premise needed
by the existing binary join-tree construction. -/
theorem BridgeData.cross_occurrence
    {F : I → HypergraphPiece W} {G : J → HypergraphPiece W}
    {i₀ : I} {j₀ : J}
    (D : BridgeData F G i₀ j₀)
    (x : W) (i : I) (j : J)
    (hFi : x ∈ (F i).carrier) (hGj : x ∈ (G j).carrier) :
    x ∈ (F i₀).carrier ∧ x ∈ (G j₀).carrier := by
  have hx : x ∈ D.port := D.cross_inside i j ⟨hFi, hGj⟩
  exact ⟨D.left_cover hx, D.right_cover hx⟩

/-- Gluing local join trees across an arbitrary (possibly multi-edge)
interface whose vertices are represented in one connector on either side
preserves the running-intersection property. -/
def BridgeData.joinTree
    [Fintype I] [Fintype J]
    {F : I → HypergraphPiece W} {G : J → HypergraphPiece W}
    {i₀ : I} {j₀ : J}
    (D : BridgeData F G i₀ j₀)
    (JF : JoinTree F) (JG : JoinTree G) :
    JoinTree (sumPieces F G) :=
  JF.sumBridge JG i₀ j₀ D.cross_occurrence

/-- Admissible cross intersections are a separate assumption: a coherent
port does not imply that two intersecting pieces share an allowed support
edge. The conclusion is the existing forest-of-copies invariant. -/
theorem BridgeData.forestOfCopies
    [Fintype I] [Fintype J]
    {F : I → HypergraphPiece W} {G : J → HypergraphPiece W}
    {i₀ : I} {j₀ : J}
    (D : BridgeData F G i₀ j₀)
    (JF : JoinTree F) (JG : JoinTree G)
    (hF : PairwiseAllowed F) (hG : PairwiseAllowed G)
    (hCrossAllowed : ∀ i j, AllowedIntersection (F i) (G j)) :
    ForestOfCopies (sumPieces F G) :=
  forestOfCopies_sumBridge JF JG hF hG i₀ j₀
    D.cross_occurrence hCrossAllowed

/-- Two vertices shared across the two families must BOTH belong to
the two chosen connector pieces, not just to the abstract port. -/
theorem BridgeData.two_shared_vertices
    {F : I → HypergraphPiece W} {G : J → HypergraphPiece W}
    {i₀ : I} {j₀ : J}
    (D : BridgeData F G i₀ j₀)
    (x y : W)
    (hx : ∃ i j, x ∈ (F i).carrier ∧ x ∈ (G j).carrier)
    (hy : ∃ i j, y ∈ (F i).carrier ∧ y ∈ (G j).carrier) :
    (x ∈ (F i₀).carrier ∧ y ∈ (F i₀).carrier) ∧
    (x ∈ (G j₀).carrier ∧ y ∈ (G j₀).carrier) := by
  obtain ⟨i, j, hxi, hxj⟩ := hx
  obtain ⟨k, l, hyk, hyl⟩ := hy
  have hxc := D.cross_occurrence x i j hxi hxj
  have hyc := D.cross_occurrence y k l hyk hyl
  exact ⟨⟨hxc.1, hyc.1⟩, ⟨hxc.2, hyc.2⟩⟩

/-- A formal obstruction to reducing a multi-helper interface to one bag.
If two vertices occur on both sides but no left member contains both,
no choice of connectors can satisfy the single-port condition.

This is WHY a genuine coherent-subtree interface is needed beyond the
current single-edge forest lemma; it makes no claim that the larger
Ramsey construction exists. -/
theorem no_single_port_of_split_shared_vertices
    {F : I → HypergraphPiece W} {G : J → HypergraphPiece W}
    (x y : W)
    (hx : ∃ i j, x ∈ (F i).carrier ∧ x ∈ (G j).carrier)
    (hy : ∃ i j, y ∈ (F i).carrier ∧ y ∈ (G j).carrier)
    (hSplit : ∀ i : I,
      ¬(x ∈ (F i).carrier ∧ y ∈ (F i).carrier)) :
    ¬ ∃ i₀ j₀, Nonempty (BridgeData F G i₀ j₀) := by
  rintro ⟨i₀, j₀, ⟨D⟩⟩
  have h := D.two_shared_vertices x y hx hy
  exact hSplit i₀ h.1

end CoherentPort
end StructuralRamsey.Girth

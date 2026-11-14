import Girth.Forest

/-!
# Restricting a running-intersection family to a vertex subset

For the small-trace lemma, a completion of ORIGINAL cover members must
remain a join-tree family after we intersect every bag with Z.  We
forget support edges because this step uses only the running-intersection
property, not A-linearity or pairwise-allowed intersections.

The tree itself and its index type are unchanged.  In particular, this
lemma does not incorrectly assert that an arbitrary *subfamily* of a
join-tree family still admits a join tree.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- The vertex trace of a hypergraph piece, with its support-edge data
forgotten.  This is enough for the join-tree occurrence condition. -/
def HypergraphPiece.traceCarrier
    (F : HypergraphPiece W) (Z : Set W) :
    HypergraphPiece Z where
  carrier := {x : Z | x.1 ∈ F.carrier}
  edges := ∅
  edge_subset_carrier := by
    intro e he
    exact False.elim he

/-- Restriction to Z preserves the SAME join tree and hence its
running-intersection condition.  This exact trace operation is used
after an internal local join-tree completion. -/
theorem JoinTree.traceCarrier
    {F : ι → HypergraphPiece W}
    (J : JoinTree F) (Z : Set W) :
    JoinTree (fun i => (F i).traceCarrier Z) where
  tree := J.tree
  isTree := J.isTree
  running := by
    intro x
    exact J.running x.1

/-- A finite family of ordinary sets, considered as a family of bags.
All support-edge sets are empty: no geometric property is smuggled
into the trace-counting proof. -/
def setBagPiece (F : Set W) : HypergraphPiece W where
  carrier := F
  edges := ∅
  edge_subset_carrier := by
    intro e he
    exact False.elim he

/-- The restricted carrier of a set bag is exactly its usual trace,
now regarded as a set of vertices of Z. -/
theorem setBagPiece_traceCarrier
    (F Z : Set W) :
    ((setBagPiece F).traceCarrier Z).carrier =
      {x : Z | x.1 ∈ F} := rfl

end StructuralRamsey.Girth

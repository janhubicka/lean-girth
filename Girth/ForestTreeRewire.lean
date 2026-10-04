import Girth.FiberConnectedTree
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Rewiring a deleted vertex of a join tree

The one-edge deletion argument replaces the star at the deleted join-tree node
by a tree on its former neighbours.  This file collects the finite graph
lemmas needed for that surgery.
-/

namespace StructuralRamsey.Girth

universe u v

variable {V : Type u} {ι : Type v}

/-- A finite connected graph with exactly one fewer edge than vertices is a
tree.  We use this after replacing the deleted star by a tree on its
neighbours. -/
theorem isTree_of_connected_card_edgeFinset
    {V : Type v} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hcard : Finset.card G.edgeFinset + 1 = Fintype.card V) :
    G.IsTree := by
  classical
  obtain ⟨T, hTG, hTtree⟩ := hconn.exists_isTree_le
  have hTcard : Finset.card T.edgeFinset + 1 = Fintype.card V :=
    hTtree.card_edgeFinset
  have hcards : Finset.card T.edgeFinset = Finset.card G.edgeFinset := by
    omega
  have hsub : T.edgeFinset ⊆ G.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.2 hTG
  have hedge : T.edgeFinset = G.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hEq : T = G :=
    SimpleGraph.edgeFinset_inj.1 hedge
  simpa [hEq] using hTtree


/-- A neighbour of the deleted vertex, viewed as a surviving vertex. -/
def JoinTree.neighborToErasedEmbedding
    {F : ι → HypergraphPiece V}
    (J : JoinTree F) (center : ι) :
    J.tree.neighborSet center ↪ {i : ι // i ∈ ({center} : Set ι)ᶜ} where
  toFun r := ⟨r.1, by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact r.2.ne.symm⟩
  inj' := fun a b h => Subtype.ext (congrArg Subtype.val h)

/-- Replace the deleted centre-star by an arbitrary graph on its former
neighbours. -/
def JoinTree.rewireAfterDelete
    {F : ι → HypergraphPiece V}
    (J : JoinTree F) (center : ι)
    (R : SimpleGraph (J.tree.neighborSet center)) :
    SimpleGraph {i : ι // i ∈ ({center} : Set ι)ᶜ} :=
  J.tree.induce (({center} : Set ι)ᶜ) ⊔
    R.map (J.neighborToErasedEmbedding center)

/-- Edges inserted between former neighbours of the deleted centre are new:
two distinct neighbours of a vertex in a tree cannot already lie in the same
component after deleting that vertex. -/
theorem JoinTree.disjoint_deletedGraph_map_neighborGraph
    {F : ι → HypergraphPiece V} [Fintype ι]
    (J : JoinTree F) (center : ι)
    (R : SimpleGraph (J.tree.neighborSet center)) :
    Disjoint
      (J.tree.induce (({center} : Set ι)ᶜ))
      (R.map (J.neighborToErasedEmbedding center)) := by
  classical
  rw [disjoint_iff_inf_le]
  intro a b hab
  change
    (J.tree.induce (({center} : Set ι)ᶜ)).Adj a b ∧
      (R.map (J.neighborToErasedEmbedding center)).Adj a b at hab
  change False
  rcases hab with ⟨hdelete, hmap⟩
  rw [SimpleGraph.map_adj] at hmap
  rcases hmap with ⟨r, s, hrs, hra, hsb⟩
  subst a
  subst b
  have hreach :
      (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        (J.neighborToErasedEmbedding center r)
        (J.neighborToErasedEmbedding center s) :=
    hdelete.reachable
  have hrsEq : r.1 = s.1 := by
    apply J.neighbor_eq_of_reachable_after_delete
      (center := center) r.2 s.2
    simpa [JoinTree.neighborToErasedEmbedding] using hreach
  exact hrs.ne (Subtype.ext hrsEq)


end StructuralRamsey.Girth

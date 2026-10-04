import Girth.FiberConnectedTree
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! # Rewiring a deleted vertex of a join tree

The one-edge deletion argument replaces the star at the deleted join-tree node
by a tree on its former neighbours.  This file collects the finite graph
lemmas needed for that surgery.
-/

namespace StructuralRamsey.Girth

universe v

variable {V ι : Type v}

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



/-- Replacing the centre-star by a connected graph on all former neighbours
keeps the surviving vertices connected. -/
theorem JoinTree.rewireAfterDelete_connected
    {F : ι → HypergraphPiece V} [Fintype ι]
    (J : JoinTree F) (center : ι)
    (R : SimpleGraph (J.tree.neighborSet center))
    (hR : R.Connected) :
    (J.rewireAfterDelete center R).Connected := by
  classical
  let e := J.neighborToErasedEmbedding center
  haveI : Nonempty (J.tree.neighborSet center) := hR.nonempty
  haveI : Nonempty {i : ι // i ∈ ({center} : Set ι)ᶜ} :=
    Nonempty.map e hR.nonempty
  refine ⟨?_⟩
  intro a b
  have ha : a.1 ≠ center := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using a.2
  have hb : b.1 ≠ center := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using b.2
  obtain ⟨ra, hra, hreachA⟩ :=
    J.exists_neighbor_reachable_after_delete ha
  obtain ⟨rb, hrb, hreachB⟩ :=
    J.exists_neighbor_reachable_after_delete hb
  let raN : J.tree.neighborSet center := ⟨ra, hra⟩
  let rbN : J.tree.neighborSet center := ⟨rb, hrb⟩
  have hA :
      (J.rewireAfterDelete center R).Reachable
        a (J.neighborToErasedEmbedding center raN) := by
    have h := hreachA.symm.mono
      (show J.tree.induce (({center} : Set ι)ᶜ) ≤
        J.rewireAfterDelete center R from le_sup_left)
    convert h using 1 <;> apply Subtype.ext <;> rfl
  have hRootsMap :
      (R.map (J.neighborToErasedEmbedding center)).Reachable
        (J.neighborToErasedEmbedding center raN)
        (J.neighborToErasedEmbedding center rbN) := by
    have h := hR raN rbN
    exact h.map
      (SimpleGraph.Embedding.map
        (J.neighborToErasedEmbedding center) R).toHom
  have hRoots :
      (J.rewireAfterDelete center R).Reachable
        (J.neighborToErasedEmbedding center raN)
        (J.neighborToErasedEmbedding center rbN) :=
    hRootsMap.mono le_sup_right
  have hB :
      (J.rewireAfterDelete center R).Reachable
        (J.neighborToErasedEmbedding center rbN) b := by
    have h := hreachB.mono
      (show J.tree.induce (({center} : Set ι)ᶜ) ≤
        J.rewireAfterDelete center R from le_sup_left)
    convert h using 1 <;> apply Subtype.ext <;> rfl
  exact hA.trans (hRoots.trans hB)


/-- The rewired graph has exactly one fewer edge than surviving vertices when
the replacement graph on the former neighbours is a tree. -/
theorem JoinTree.rewireAfterDelete_card_edgeFinset
    {F : ι → HypergraphPiece V} [Fintype ι]
    (J : JoinTree F) (center : ι)
    (R : SimpleGraph (J.tree.neighborSet center))
    (hR : R.IsTree) :
    Finset.card (J.rewireAfterDelete center R).edgeFinset + 1 =
      Fintype.card ι - 1 := by
  classical
  let D := J.tree.induce (({center} : Set ι)ᶜ)
  let e := J.neighborToErasedEmbedding center
  let M := R.map e
  have hdisjGraph : Disjoint D M := by
    simpa [D, M, e] using
      J.disjoint_deletedGraph_map_neighborGraph center R
  have hdisj : Disjoint D.edgeFinset M.edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr hdisjGraph
  have hsup :
      Finset.card (J.rewireAfterDelete center R).edgeFinset =
        Finset.card D.edgeFinset + Finset.card M.edgeFinset := by
    rw [JoinTree.rewireAfterDelete, SimpleGraph.edgeFinset_sup,
      Finset.card_union_of_disjoint hdisj]
  have hDcard :
      Finset.card D.edgeFinset =
        Finset.card J.tree.edgeFinset - J.tree.degree center := by
    dsimp [D]
    rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
      SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  have hMcard :
      Finset.card M.edgeFinset = Finset.card R.edgeFinset := by
    dsimp [M]
    exact SimpleGraph.card_edgeFinset_map e R
  have hJcard :
      Finset.card J.tree.edgeFinset + 1 = Fintype.card ι :=
    J.isTree.card_edgeFinset
  have hRcard :
      Finset.card R.edgeFinset + 1 =
        Fintype.card (J.tree.neighborSet center) :=
    hR.card_edgeFinset
  have hNcard :
      Fintype.card (J.tree.neighborSet center) =
        J.tree.degree center :=
    J.tree.card_neighborSet_eq_degree center
  have hdeg :
      J.tree.degree center ≤ Finset.card J.tree.edgeFinset :=
    J.tree.degree_le_card_edgeFinset
  rw [hsup, hDcard, hMcard]
  omega


/-- Replacing one vertex of a join tree by any tree on its former neighbours
again gives a tree on the surviving vertices. -/
theorem JoinTree.rewireAfterDelete_isTree
    {F : ι → HypergraphPiece V} [Fintype ι]
    (J : JoinTree F) (center : ι)
    (R : SimpleGraph (J.tree.neighborSet center))
    (hR : R.IsTree) :
    (J.rewireAfterDelete center R).IsTree := by
  classical
  apply isTree_of_connected_card_edgeFinset
    (J.rewireAfterDelete center R)
  · exact J.rewireAfterDelete_connected center R hR.connected
  · rw [J.rewireAfterDelete_card_edgeFinset center R hR,
      Fintype.card_compl_set]
    simp

end StructuralRamsey.Girth

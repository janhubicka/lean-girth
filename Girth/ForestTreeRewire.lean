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


/-- Instance-independent version of the finite edge-count criterion. -/
theorem isTree_of_connected_ncard_edgeSet
    {V : Type v} [Finite V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hcard : G.edgeSet.ncard + 1 = Nat.card V) :
    G.IsTree := by
  classical
  letI := Fintype.ofFinite V
  haveI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  have hedge : Finset.card G.edgeFinset = G.edgeSet.ncard := by
    calc
      Finset.card G.edgeFinset = Fintype.card G.edgeSet :=
        G.edgeFinset_card
      _ = G.edgeSet.ncard :=
        Set.fintypeCard_eq_ncard G.edgeSet
  apply isTree_of_connected_card_edgeFinset G hconn
  rw [hedge, ← Nat.card_eq_fintype_card]
  exact hcard


/-- A neighbour of the deleted vertex, viewed as a surviving vertex. -/
def JoinTree.neighborToErasedEmbedding
    {F : ι → HypergraphPiece V}
    (J : JoinTree F) (center : ι) :
    J.tree.neighborSet center ↪ {i : ι // i ∈ ({center} : Set ι)ᶜ} where
  toFun r := ⟨r.1, by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact r.2.ne.symm⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact congrArg
      (fun z : {i : ι // i ∈ ({center} : Set ι)ᶜ} => z.1) h

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
  have hreach' :
      (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        ⟨r.1, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
            using r.2.ne.symm⟩
        ⟨s.1, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
            using s.2.ne.symm⟩ := by
    convert hreach using 1 <;> apply Subtype.ext <;> rfl
  have hrsEq : r.1 = s.1 := by
    exact J.neighbor_eq_of_reachable_after_delete
      (center := center) r.2 s.2 hreach'
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


/-- Replacing one vertex of a join tree by any tree on its former neighbours
again gives a tree on the surviving vertices. -/
theorem JoinTree.rewireAfterDelete_isTree
    {F : ι → HypergraphPiece V} [Fintype ι]
    (J : JoinTree F) (center : ι)
    (R : SimpleGraph (J.tree.neighborSet center))
    (hR : R.IsTree) :
    (J.rewireAfterDelete center R).IsTree := by
  classical
  let D := J.tree.induce (({center} : Set ι)ᶜ)
  let e := J.neighborToErasedEmbedding center
  let M := R.map e
  have hdisjGraph : Disjoint D M := by
    simpa [D, M, e] using
      J.disjoint_deletedGraph_map_neighborGraph center R
  have hDedge : Finset.card D.edgeFinset = D.edgeSet.ncard := by
    calc
      Finset.card D.edgeFinset = Fintype.card D.edgeSet := D.edgeFinset_card
      _ = D.edgeSet.ncard := Set.fintypeCard_eq_ncard D.edgeSet
  have hJedge :
      Finset.card J.tree.edgeFinset = J.tree.edgeSet.ncard := by
    calc
      Finset.card J.tree.edgeFinset = Fintype.card J.tree.edgeSet :=
        J.tree.edgeFinset_card
      _ = J.tree.edgeSet.ncard :=
        Set.fintypeCard_eq_ncard J.tree.edgeSet
  have hDcard :
      D.edgeSet.ncard =
        J.tree.edgeSet.ncard - J.tree.degree center := by
    have h1 :=
      SimpleGraph.card_edgeFinset_induce_compl_singleton J.tree center
    have h2 :=
      SimpleGraph.card_edgeFinset_deleteIncidenceSet J.tree center
    rw [h2] at h1
    calc
      D.edgeSet.ncard = Finset.card D.edgeFinset := hDedge.symm
      _ = Finset.card J.tree.edgeFinset - J.tree.degree center := by
        simpa [D] using h1
      _ = J.tree.edgeSet.ncard - J.tree.degree center := by
        rw [hJedge]
  have hMcard : M.edgeSet.ncard = R.edgeSet.ncard := by
    dsimp [M]
    rw [SimpleGraph.edgeSet_map]
    exact Set.ncard_image_of_injective _ e.sym2Map.injective
  have hJcard : J.tree.edgeSet.ncard + 1 = Nat.card ι := by
    calc
      J.tree.edgeSet.ncard + 1 =
          Finset.card J.tree.edgeFinset + 1 := by rw [hJedge]
      _ = Fintype.card ι := J.isTree.card_edgeFinset
      _ = Nat.card ι := by rw [Nat.card_eq_fintype_card]
  have hRedge : Finset.card R.edgeFinset = R.edgeSet.ncard := by
    calc
      Finset.card R.edgeFinset = Fintype.card R.edgeSet := R.edgeFinset_card
      _ = R.edgeSet.ncard := Set.fintypeCard_eq_ncard R.edgeSet
  have hRcard :
      R.edgeSet.ncard + 1 = Nat.card (J.tree.neighborSet center) := by
    calc
      R.edgeSet.ncard + 1 = Finset.card R.edgeFinset + 1 := by rw [hRedge]
      _ = Fintype.card (J.tree.neighborSet center) := hR.card_edgeFinset
      _ = Nat.card (J.tree.neighborSet center) := by
        rw [Nat.card_eq_fintype_card]
  have hNcard :
      Nat.card (J.tree.neighborSet center) = J.tree.degree center := by
    simpa [Nat.card_eq_fintype_card] using
      J.tree.card_neighborSet_eq_degree center
  have hdeg :
      J.tree.degree center ≤ J.tree.edgeSet.ncard := by
    rw [← SimpleGraph.ncard_incidenceSet]
    exact Set.ncard_le_ncard
      (J.tree.incidenceSet_subset center)
      (Set.toFinite J.tree.edgeSet)
  have hrewireCard :
      (J.rewireAfterDelete center R).edgeSet.ncard + 1 =
        Nat.card {i : ι // i ∈ ({center} : Set ι)ᶜ} := by
    have hsup :
        (J.rewireAfterDelete center R).edgeSet =
          D.edgeSet ∪ M.edgeSet := by
      simp [JoinTree.rewireAfterDelete, D, M, e, SimpleGraph.edgeSet_sup]
    have hdisjEdge : Disjoint D.edgeSet M.edgeSet :=
      SimpleGraph.disjoint_edgeSet.mpr hdisjGraph
    rw [hsup, Set.ncard_union_eq hdisjEdge, hDcard, hMcard]
    have hsurv :
        Nat.card {i : ι // i ∈ ({center} : Set ι)ᶜ} =
          Nat.card ι - 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
      simp
    rw [hsurv]
    omega
  exact isTree_of_connected_ncard_edgeSet
    (J.rewireAfterDelete center R)
    (J.rewireAfterDelete_connected center R hR.connected)
    hrewireCard

end StructuralRamsey.Girth

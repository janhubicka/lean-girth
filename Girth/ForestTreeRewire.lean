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
  obtain ⟨T, hTG, hTtree⟩ := hconn.exists_isTree_le
  have hTedge :
      Finset.card T.edgeFinset = T.edgeSet.ncard := by
    calc
      Finset.card T.edgeFinset = Fintype.card T.edgeSet :=
        T.edgeFinset_card
      _ = T.edgeSet.ncard :=
        Set.fintypeCard_eq_ncard T.edgeSet
  have hTcard : T.edgeSet.ncard + 1 = Nat.card V := by
    calc
      T.edgeSet.ncard + 1 =
          Finset.card T.edgeFinset + 1 :=
        congrArg (· + 1) hTedge.symm
      _ = Fintype.card V := hTtree.card_edgeFinset
      _ = Nat.card V := by simp
  have hcards : T.edgeSet.ncard = G.edgeSet.ncard := by
    omega
  have hsub : T.edgeSet ⊆ G.edgeSet :=
    SimpleGraph.edgeSet_mono hTG
  have hedge : T.edgeSet = G.edgeSet :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite G.edgeSet)
  have hEq : T = G :=
    SimpleGraph.edgeSet_injective hedge
  simpa [hEq] using hTtree


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



/-- If an ambient vertex is absent from the deleted member, its whole
old occurrence subtree survives the deletion. -/
theorem JoinTree.reachable_occurrence_after_delete_of_not_mem_center
    {F : ι → HypergraphPiece V}
    (J : JoinTree F)
    {center i j : ι}
    (hi : i ≠ center) (hj : j ≠ center)
    {x : V}
    (hxi : x ∈ (F i).carrier)
    (hxj : x ∈ (F j).carrier)
    (hxCenter : x ∉ (F center).carrier) :
    ((J.tree.induce (({center} : Set ι)ᶜ)).induce
      {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ (F k.1).carrier}).Reachable
        ⟨⟨i, by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩,
          hxi⟩
        ⟨⟨j, by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hj⟩,
          hxj⟩ := by
  let occ : Set ι := {k : ι | x ∈ (F k).carrier}
  let iOcc : occ := ⟨i, hxi⟩
  let jOcc : occ := ⟨j, hxj⟩
  let phi :
      (J.tree.induce occ) →g
        ((J.tree.induce (({center} : Set ι)ᶜ)).induce
          {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ (F k.1).carrier}) :=
    { toFun := fun z =>
        ⟨⟨z.1, by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            intro hz
            subst hz
            exact hxCenter z.2⟩,
          z.2⟩
      map_rel' := by
        intro a b hab
        exact hab }
  have h := (J.running x iOcc jOcc).map phi
  convert h using 1 <;> apply Subtype.ext <;> apply Subtype.ext <;> rfl


/-- Inside a fixed component of the deleted tree, the unique path
between two occurrences of an ambient vertex still consists entirely of
occurrences of that vertex. -/
theorem JoinTree.reachable_occurrence_after_delete
    {F : ι → HypergraphPiece V}
    (J : JoinTree F)
    {center i j : ι}
    (hi : i ≠ center) (hj : j ≠ center)
    {x : V}
    (hxi : x ∈ (F i).carrier)
    (hxj : x ∈ (F j).carrier)
    (hdel :
      (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        ⟨i, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩
        ⟨j, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hj⟩) :
    ((J.tree.induce (({center} : Set ι)ᶜ)).induce
      {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ (F k.1).carrier}).Reachable
        ⟨⟨i, by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩,
          hxi⟩
        ⟨⟨j, by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hj⟩,
          hxj⟩ := by
  obtain ⟨q0, hq0⟩ := hdel.exists_isPath
  let delInc :
      (J.tree.induce (({center} : Set ι)ᶜ)) →g J.tree :=
    { toFun := fun z => z.1
      map_rel' := by
        intro a b hab
        exact hab }
  let q : J.tree.Walk i j := q0.map delInc
  have hq : q.IsPath := by
    dsimp [q]
    exact hq0.map (fun a b h => Subtype.ext h)

  let occ : Set ι := {k : ι | x ∈ (F k).carrier}
  let iOcc : occ := ⟨i, hxi⟩
  let jOcc : occ := ⟨j, hxj⟩
  obtain ⟨p0, hp0⟩ := (J.running x iOcc jOcc).exists_isPath
  let occInc : (J.tree.induce occ) →g J.tree :=
    { toFun := fun z => z.1
      map_rel' := by
        intro a b hab
        exact hab }
  let p : J.tree.Walk i j := p0.map occInc
  have hp : p.IsPath := by
    dsimp [p]
    exact hp0.map (fun a b h => Subtype.ext h)
  have hpq : p = q :=
    (J.isTree.existsUnique_path i j).unique hp hq

  have hqX :
      ∀ z ∈ q0.support, x ∈ (F z.1).carrier := by
    intro z hz
    have hzq : z.1 ∈ q.support := by
      dsimp [q, delInc]
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨z, hz, rfl⟩
    rw [← hpq] at hzq
    dsimp [p, occInc] at hzq
    rw [SimpleGraph.Walk.support_map] at hzq
    rcases List.mem_map.mp hzq with ⟨w, hw, hwval⟩
    have hwx : x ∈ (F w.1).carrier := w.2
    change w.1 = z.1 at hwval
    rw [← hwval]
    exact hwx
  let qx := q0.induce {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ (F k.1).carrier} hqX
  have hqx := qx.reachable
  convert hqx using 1 <;> apply Subtype.ext <;> apply Subtype.ext <;> rfl


/-- The attachment label of a former neighbour is its carrier
intersection with the deleted member. -/
def JoinTree.neighborAttachment
    {F : ι → HypergraphPiece V}
    (J : JoinTree F) (center : ι)
    (r : J.tree.neighborSet center) : Set V :=
  (F center).carrier ∩ (F r.1).carrier

/-- In the no-full-edge case, every neighbour attachment is empty or a
singleton. -/
theorem JoinTree.neighborAttachment_subsingleton
    {F : ι → HypergraphPiece V}
    (J : JoinTree F)
    (hPair : PairwiseAllowed F)
    {center : ι}
    (hOne : (F center).IsOneEdge)
    (hNoFull :
      ∀ k : ι, k ≠ center →
        ¬ (F center).carrier ⊆ (F k).carrier)
    (r : J.tree.neighborSet center) :
    (J.neighborAttachment center r).Subsingleton := by
  have h :=
    HypergraphPiece.isOneEdge_allowed_dichotomy
      hOne (hPair r.2.ne)
  exact h.resolve_right (hNoFull r.1 r.2.ne.symm)

/-- Two neighbour attachments containing the same vertex of the deleted
one-edge member are equal. -/
theorem JoinTree.neighborAttachment_eq_of_common
    {F : ι → HypergraphPiece V}
    (J : JoinTree F)
    (hPair : PairwiseAllowed F)
    {center : ι}
    (hOne : (F center).IsOneEdge)
    (hNoFull :
      ∀ k : ι, k ≠ center →
        ¬ (F center).carrier ⊆ (F k).carrier)
    {r s : J.tree.neighborSet center}
    {x : V}
    (hxCenter : x ∈ (F center).carrier)
    (hxr : x ∈ (F r.1).carrier)
    (hxs : x ∈ (F s.1).carrier) :
    J.neighborAttachment center r =
      J.neighborAttachment center s := by
  have hrsub :=
    J.neighborAttachment_subsingleton hPair hOne hNoFull r
  have hssub :=
    J.neighborAttachment_subsingleton hPair hOne hNoFull s
  apply Set.Subset.antisymm
  · intro y hy
    have hyx : y = x :=
      hrsub hy ⟨hxCenter, hxr⟩
    simpa [hyx] using (show x ∈ J.neighborAttachment center s from
      ⟨hxCenter, hxs⟩)
  · intro y hy
    have hyx : y = x :=
      hssub hy ⟨hxCenter, hxs⟩
    simpa [hyx] using (show x ∈ J.neighborAttachment center r from
      ⟨hxCenter, hxr⟩)


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


/-- In the no-full-edge case, deleting a one-edge member from a nonempty
remaining family admits a new join tree.  The deleted star is replaced by a
tree on its former neighbours whose fibres are the attachment intersections. -/
theorem JoinTree.nonempty_eraseOneEdgeNoFull
    {F : ι → HypergraphPiece V} [Fintype ι]
    (J : JoinTree F)
    (hPair : PairwiseAllowed F)
    {center : ι}
    (hOne : (F center).IsOneEdge)
    (hNoFull :
      ∀ k : ι, k ≠ center →
        ¬ (F center).carrier ⊆ (F k).carrier)
    [Nonempty {i : ι // i ∈ (({center} : Set ι)ᶜ)}] :
    Nonempty (JoinTree (erasePiece F center)) := by
  classical
  let survivor := {i : ι // i ∈ (({center} : Set ι)ᶜ)}
  let i0 : survivor :=
    Classical.choice (inferInstance : Nonempty survivor)
  have hi0 : i0.1 ≠ center := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using i0.2
  obtain ⟨root0, hroot0, _hreach0⟩ :=
    J.exists_neighbor_reachable_after_delete hi0
  let rootN0 : J.tree.neighborSet center := ⟨root0, hroot0⟩
  letI : Nonempty (J.tree.neighborSet center) := ⟨rootN0⟩
  obtain ⟨R, hRtree, hFib⟩ :=
    exists_tree_fibers_preconnected
      (J.neighborAttachment center)
  refine
    ⟨{ tree := J.rewireAfterDelete center R
       isTree := J.rewireAfterDelete_isTree center R hRtree
       running := ?_ }⟩
  intro x
  change
    ((J.rewireAfterDelete center R).induce
      {k : survivor | x ∈ (F k.1).carrier}).Preconnected
  intro a b
  have ha : a.1.1 ≠ center := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using a.1.2
  have hb : b.1.1 ≠ center := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using b.1.2
  have hmono :
      ((J.tree.induce (({center} : Set ι)ᶜ)).induce
        {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ (F k.1).carrier}) ≤
      ((J.rewireAfterDelete center R).induce
        {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ (F k.1).carrier}) := by
    exact SimpleGraph.induce_mono
      (show J.tree.induce (({center} : Set ι)ᶜ) ≤
        J.rewireAfterDelete center R from le_sup_left)
      Set.Subset.rfl
  by_cases hxCenter : x ∈ (F center).carrier
  · obtain ⟨ra, hra, hreachA⟩ :=
      J.exists_neighbor_reachable_after_delete ha
    obtain ⟨rb, hrb, hreachB⟩ :=
      J.exists_neighbor_reachable_after_delete hb
    let raN : J.tree.neighborSet center := ⟨ra, hra⟩
    let rbN : J.tree.neighborSet center := ⟨rb, hrb⟩
    have hxra : x ∈ (F ra).carrier :=
      J.mem_root_of_mem_center_and_reachable_after_delete
        hra ha hreachA hxCenter a.2
    have hxrb : x ∈ (F rb).carrier :=
      J.mem_root_of_mem_center_and_reachable_after_delete
        hrb hb hreachB hxCenter b.2
    have hOccA :=
      J.reachable_occurrence_after_delete
        hra.ne.symm ha hxra a.2 hreachA
    have hOccB :=
      J.reachable_occurrence_after_delete
        hrb.ne.symm hb hxrb b.2 hreachB
    have hA :
        ((J.rewireAfterDelete center R).induce
          {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ (F k.1).carrier}).Reachable
          a
          ⟨J.neighborToErasedEmbedding center raN, hxra⟩ := by
      have h := (hOccA.mono hmono).symm
      convert h using 1 <;> apply Subtype.ext <;>
        apply Subtype.ext <;> rfl
    have hB :
        ((J.rewireAfterDelete center R).induce
          {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ (F k.1).carrier}).Reachable
          ⟨J.neighborToErasedEmbedding center rbN, hxrb⟩
          b := by
      have h := hOccB.mono hmono
      convert h using 1 <;> apply Subtype.ext <;>
        apply Subtype.ext <;> rfl
    have hLabel :
        J.neighborAttachment center raN =
          J.neighborAttachment center rbN :=
      J.neighborAttachment_eq_of_common
        hPair hOne hNoFull hxCenter hxra hxrb
    let raF :
        {r : J.tree.neighborSet center |
          J.neighborAttachment center r =
            J.neighborAttachment center raN} :=
      ⟨raN, rfl⟩
    let rbF :
        {r : J.tree.neighborSet center |
          J.neighborAttachment center r =
            J.neighborAttachment center raN} :=
      ⟨rbN, hLabel.symm⟩
    have hRroots :
        (R.induce
          {r |
            J.neighborAttachment center r =
              J.neighborAttachment center raN}).Reachable
          raF rbF :=
      hFib (J.neighborAttachment center raN) raF rbF
    let phi :
        (R.induce
          {r |
            J.neighborAttachment center r =
              J.neighborAttachment center raN}) →g
        ((J.rewireAfterDelete center R).induce
          {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ (F k.1).carrier}) :=
      { toFun := fun z =>
          ⟨J.neighborToErasedEmbedding center z.1,
            by
              have hxBase :
                  x ∈ J.neighborAttachment center raN :=
                ⟨hxCenter, hxra⟩
              have hxHere :
                  x ∈ J.neighborAttachment center z.1 := by
                rw [z.2]
                exact hxBase
              exact hxHere.2⟩
        map_rel' := by
          intro z w hzw
          change (J.rewireAfterDelete center R).Adj
            (J.neighborToErasedEmbedding center z.1)
            (J.neighborToErasedEmbedding center w.1)
          apply le_sup_right
          simpa using hzw }
    have hRoots0 := hRroots.map phi
    have hRoots :
        ((J.rewireAfterDelete center R).induce
          {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ (F k.1).carrier}).Reachable
          ⟨J.neighborToErasedEmbedding center raN, hxra⟩
          ⟨J.neighborToErasedEmbedding center rbN, hxrb⟩ := by
      convert hRoots0 using 1 <;> apply Subtype.ext <;>
        apply Subtype.ext <;> rfl
    exact hA.trans (hRoots.trans hB)
  · have h :=
      J.reachable_occurrence_after_delete_of_not_mem_center
        ha hb a.2 b.2 hxCenter
    exact h.mono hmono


/-- Therefore a one-edge member can be deleted from a finite forest whenever
no remaining member contains its whole carrier. -/
theorem ForestOfCopies.erase_oneEdge_of_no_full
    {F : ι → HypergraphPiece V} [Fintype ι]
    (hF : ForestOfCopies F)
    (J : JoinTree F)
    {center : ι}
    (hOne : (F center).IsOneEdge)
    (hNoFull :
      ∀ k : ι, k ≠ center →
        ¬ (F center).carrier ⊆ (F k).carrier) :
    ForestOfCopies (erasePiece F center) := by
  refine
    ⟨JoinTree.pairwiseAllowed_erase hF.pairwiseAllowed center, ?_⟩
  let survivor := {i : ι // i ∈ (({center} : Set ι)ᶜ)}
  by_cases hN : Nonempty survivor
  · letI : Nonempty survivor := hN
    exact Or.inr
      (J.nonempty_eraseOneEdgeNoFull
        hF.pairwiseAllowed hOne hNoFull)
  · left
    exact
      ⟨fun z => hN ⟨z⟩⟩

end StructuralRamsey.Girth

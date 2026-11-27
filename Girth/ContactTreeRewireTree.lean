import Girth.ContactTreeRewire

namespace StructuralRamsey.Girth
universe v
variable {V ι : Type v}

/-- Replacing the centre-star by a connected graph on all former neighbours
keeps the surviving vertices connected. -/
theorem ContactJoinTree.rewireAfterDelete_connected
    {F : ι → Set V} [Fintype ι]
    (J : ContactJoinTree F) (center : ι)
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
theorem ContactJoinTree.rewireAfterDelete_isTree
    {F : ι → Set V} [Fintype ι]
    (J : ContactJoinTree F) (center : ι)
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
      simp [ContactJoinTree.rewireAfterDelete, D, M, e, SimpleGraph.edgeSet_sup]
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
  exact contact_isTree_of_connected_ncard_edgeSet
    (J.rewireAfterDelete center R)
    (J.rewireAfterDelete_connected center R hR.connected)
    hrewireCard

end StructuralRamsey.Girth

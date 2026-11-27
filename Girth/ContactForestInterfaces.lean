import Girth.ForestCarrierCorner

/-! # Forests specified by allowed separators on tree links

In a linear ambient hypergraph, running intersection propagates two shared
vertices along the unique tree path. Every link on that path therefore has
the same separating edge. Thus the manuscript's condition on tree links
implies the pairwise condition in `ForestOfCopies`.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- Every piece on the unique path contains each vertex shared by its
endpoints. -/
theorem JoinTree.mem_of_mem_path
    {F : I → HypergraphPiece W} (J : JoinTree F)
    {i j k : I} (p : J.tree.Walk i j) (hp : p.IsPath)
    (hk : k ∈ p.support) {x : W}
    (hi : x ∈ (F i).carrier) (hj : x ∈ (F j).carrier) :
    x ∈ (F k).carrier := by
  let S : Set I := {i | x ∈ (F i).carrier}
  obtain ⟨q,hq⟩ := (J.running x (⟨i,hi⟩ : S) (⟨j,hj⟩ : S)).exists_isPath
  let inc : (J.tree.induce S) →g J.tree := {
    toFun := Subtype.val
    map_rel' := fun h => h }
  have hmap : (q.map inc).IsPath := hq.map Subtype.val_injective
  have he : q.map inc = p := (J.isTree.existsUnique_path i j).unique hmap hp
  rw [← he,SimpleGraph.Walk.support_map] at hk
  obtain ⟨z,_,hzk⟩ := List.mem_map.mp hk
  change z.val = k at hzk
  exact hzk ▸ z.property

/-- In a linear ambient hypergraph, allowed intersections on the links
of a join tree force allowed intersections between every distinct pair. -/
theorem JoinTree.pairwiseAllowed_of_links
    {F : I → HypergraphPiece W} (J : JoinTree F)
    (H : Set (Set W)) (hLinear : LinearEdgeSet H)
    (hEdges : ∀ i, (F i).edges ⊆ H)
    (hLinks : ∀ {i j}, J.tree.Adj i j → AllowedIntersection (F i) (F j)) :
    PairwiseAllowed F := by
  have aux : ∀ {i j : I} (p : J.tree.Walk i j),
      p.IsPath → i ≠ j → AllowedIntersection (F i) (F j) := by
    intro i j p
    induction p with
    | nil =>
      intro _ hne
      exact (hne rfl).elim
    | @cons i k j h p ih =>
      intro hp _
      by_cases hkj : k = j
      · subst j
        exact hLinks h
      by_cases hsmall : ((F i).carrier ∩ (F j).carrier).Subsingleton
      · exact Or.inl hsmall
      have hmiddle : (F i).carrier ∩ (F j).carrier ⊆ (F k).carrier := by
        intro x hx
        exact J.mem_of_mem_path (.cons h p) hp
          (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons];
              exact Or.inr p.start_mem_support) hx.1 hx.2
      have hleft : (F i).carrier ∩ (F j).carrier ⊆
          (F i).carrier ∩ (F k).carrier := fun _ hx => ⟨hx.1,hmiddle hx⟩
      have hright : (F i).carrier ∩ (F j).carrier ⊆
          (F k).carrier ∩ (F j).carrier := fun _ hx => ⟨hmiddle hx,hx.2⟩
      rcases hLinks h with hs | ⟨e,hei,hek,he⟩
      · exact (hsmall (fun x hx y hy => hs (hleft hx) (hleft hy))).elim
      rcases ih hp.of_cons hkj with hs | ⟨f,hfk,hfj,hf⟩
      · exact (hsmall (fun x hx y hy => hs (hright hx) (hright hy))).elim
      have hsube : (F i).carrier ∩ (F j).carrier ⊆ e := he ▸ hleft
      have hsubf : (F i).carrier ∩ (F j).carrier ⊆ f := hf ▸ hright
      have hef : e = f := by
        by_contra hne
        have hs := hLinear (hEdges i hei) (hEdges k hfk) hne
        exact hsmall (fun x hx y hy => hs ⟨hsube hx,hsubf hx⟩ ⟨hsube hy,hsubf hy⟩)
      refine Or.inr ⟨e,hei,hef.symm ▸ hfj,Set.Subset.antisymm hsube ?_⟩
      intro x hx
      exact ⟨(F i).edge_subset hei hx,(F j).edge_subset hfj (hef ▸ hx)⟩
  intro i j hne
  obtain ⟨p,hp,_⟩ := J.isTree.existsUnique_path i j
  exact aux p hp hne

/-- Exact equivalence between the manuscript's link condition and the
pairwise `ForestOfCopies` interface, including the empty family. -/
theorem contact_forestOfCopies_iff_linkAllowed
    (F : I → HypergraphPiece W) (H : Set (Set W))
    (hLinear : LinearEdgeSet H) (hEdges : ∀ i, (F i).edges ⊆ H) :
    ForestOfCopies F ↔ IsEmpty I ∨
      ∃ J : JoinTree F, ∀ {i j}, J.tree.Adj i j → AllowedIntersection (F i) (F j) := by
  constructor
  · rintro ⟨hpair,hEmpty | hJ⟩
    · exact Or.inl hEmpty
    · obtain ⟨J⟩ := hJ
      exact Or.inr ⟨J,fun h => hpair h.ne⟩
  · rintro (hEmpty | ⟨J,hLinks⟩)
    · exact ⟨fun {i} => (hEmpty.false i).elim,Or.inl hEmpty⟩
    · exact ⟨J.pairwiseAllowed_of_links H hLinear hEdges hLinks,Or.inr ⟨J⟩⟩

end StructuralRamsey.Girth

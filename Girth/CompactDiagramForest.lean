import Girth.ForestCarrierCorner

/-!
# Allowed link intersections suffice in a linear ambient hypergraph

The compact diagram formulation checks full intersections only at links of a
join tree.  This file proves that it implies the existing all-pairs
`ForestOfCopies` interface.  The hypothesis that every piece edge belongs to
one linear ambient edge family is essential.  No quotient realization theorem
is asserted here: `JoinTree.running` is the occurrence-connectivity condition.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v} {F : ι → HypergraphPiece W}

/-- Running intersection propagates any shared point along the unique path.
This uses only the existing join-tree data, with no intersection assumptions. -/
theorem JoinTree.compact_mem_carrier_of_mem_path
    (J : JoinTree F) {i j k : ι} (p : J.tree.Walk i j)
    (hp : p.IsPath) (hk : k ∈ p.support) {x : W}
    (hxi : x ∈ (F i).carrier) (hxj : x ∈ (F j).carrier) :
    x ∈ (F k).carrier := by
  let occ : Set ι := {s | x ∈ (F s).carrier}
  obtain ⟨q, hq⟩ := (J.running x ⟨i, hxi⟩ ⟨j, hxj⟩).exists_isPath
  let inc : (J.tree.induce occ) →g J.tree :=
    { toFun := Subtype.val
      map_rel' := fun h => h }
  have hqPath : (q.map inc).IsPath := hq.map (fun _ _ h => Subtype.ext h)
  have hEq : q.map inc = p :=
    (J.isTree.existsUnique_path i j).unique hqPath hp
  rw [← hEq, SimpleGraph.Walk.support_map] at hk
  obtain ⟨z, _, hz⟩ := List.mem_map.mp hk
  change z.val = k at hz
  exact hz ▸ z.property

/-- If each tree link has an allowed full intersection and all piece edges
are edges of a common linear ambient hypergraph, every pair has an allowed
full intersection.  In the non-singleton case, compare the first and last
path separators: running intersection puts every common point in both,
and ambient linearity forces the two separator edges to coincide. -/
theorem JoinTree.pairwiseAllowed_of_linkAllowed_of_linear
    (J : JoinTree F) (E : Set (Set W)) (hLinear : LinearEdgeSet E)
    (hEdges : ∀ i, (F i).edges ⊆ E)
    (hLink : ∀ ⦃i j⦄, J.tree.Adj i j → AllowedIntersection (F i) (F j)) :
    PairwiseAllowed F := by
  classical
  intro i j hij
  by_cases hSmall : ((F i).carrier ∩ (F j).carrier).Subsingleton
  · exact Or.inl hSmall
  obtain ⟨p, hp, _⟩ := J.isTree.existsUnique_path i j
  have hFirst := p.adj_snd (SimpleGraph.Walk.not_nil_of_ne hij)
  have hLast := p.reverse.adj_snd (SimpleGraph.Walk.not_nil_of_ne hij.symm)
  have hSubFirst : (F i).carrier ∩ (F j).carrier ⊆
      (F i).carrier ∩ (F p.snd).carrier := by
    intro x hx
    exact ⟨hx.1, J.compact_mem_carrier_of_mem_path p hp
      (p.getVert_mem_support 1) hx.1 hx.2⟩
  have hSubLast : (F i).carrier ∩ (F j).carrier ⊆
      (F j).carrier ∩ (F p.reverse.snd).carrier := by
    intro x hx
    exact ⟨hx.2, J.compact_mem_carrier_of_mem_path p.reverse hp.reverse
      (p.reverse.getVert_mem_support 1) hx.2 hx.1⟩
  obtain ⟨e, hei, _, hFirstEq⟩ := (hLink hFirst).resolve_left
    (fun hs => hSmall (Set.Subsingleton.anti hs hSubFirst))
  obtain ⟨f, hfj, _, hLastEq⟩ := (hLink hLast).resolve_left
    (fun hs => hSmall (Set.Subsingleton.anti hs hSubLast))
  have hSubE : (F i).carrier ∩ (F j).carrier ⊆ e := by
    simpa only [hFirstEq] using hSubFirst
  have hSubF : (F i).carrier ∩ (F j).carrier ⊆ f := by
    simpa only [hLastEq] using hSubLast
  have hef : e = f := by
    by_contra hne
    exact hSmall (Set.Subsingleton.anti (hLinear (hEdges i hei) (hEdges j hfj) hne)
      (fun _ hx => ⟨hSubE hx, hSubF hx⟩))
  have hej : e ∈ (F j).edges := by simpa only [hef] using hfj
  exact Or.inr ⟨e, hei, hej, Set.Subset.antisymm hSubE
    (fun _ hx => ⟨(F i).edge_subset hei hx, (F j).edge_subset hej hx⟩)⟩

/-- The compact, link-local condition yields the old forest API. -/
theorem JoinTree.forestOfCopies_of_linkAllowed_of_linear
    (J : JoinTree F) (E : Set (Set W)) (hLinear : LinearEdgeSet E)
    (hEdges : ∀ i, (F i).edges ⊆ E)
    (hLink : ∀ ⦃i j⦄, J.tree.Adj i j → AllowedIntersection (F i) (F j)) :
    ForestOfCopies F :=
  ⟨J.pairwiseAllowed_of_linkAllowed_of_linear E hLinear hEdges hLink,
    Or.inr ⟨J⟩⟩

/-- A physical edge containing at least two points has connected occurrences
as an actual member edge, not merely as a subset of the member carriers. -/
theorem JoinTree.edge_occurrence_preconnected_of_linkAllowed_of_linear
    (J : JoinTree F) (E : Set (Set W)) (hLinear : LinearEdgeSet E)
    (hEdges : ∀ i, (F i).edges ⊆ E)
    (hLink : ∀ ⦃i j⦄, J.tree.Adj i j → AllowedIntersection (F i) (F j))
    (e : Set W) (hBig : ¬e.Subsingleton) :
    (J.tree.induce {i | e ∈ (F i).edges}).Preconnected := by
  classical
  intro i j
  obtain ⟨p, hp, _⟩ := J.isTree.existsUnique_path i.val j.val
  have hPath : ∀ k ∈ p.support, e ∈ (F k).edges := by
    intro k hk
    by_cases hik : i.val = k
    · exact hik ▸ i.property
    have hSub : e ⊆ (F i.val).carrier ∩ (F k).carrier := by
      intro x hx
      exact ⟨(F i.val).edge_subset i.property hx,
        J.compact_mem_carrier_of_mem_path p hp hk
          ((F i.val).edge_subset i.property hx)
          ((F j.val).edge_subset j.property hx)⟩
    have hAllowed := J.pairwiseAllowed_of_linkAllowed_of_linear E hLinear hEdges hLink hik
    obtain ⟨d, hdi, hdk, hEq⟩ := hAllowed.resolve_left
      (fun hs => hBig (Set.Subsingleton.anti hs hSub))
    have hSubD : e ⊆ d := by simpa only [hEq] using hSub
    have hed : e = d := by
      by_contra hne
      exact hBig (Set.Subsingleton.anti
        (hLinear (hEdges i.val i.property) (hEdges i.val hdi) hne)
        (fun _ hx => ⟨hx, hSubD hx⟩))
    simpa only [hed] using hdk
  exact (p.induce {k | e ∈ (F k).edges} hPath).reachable

/-- Equivalence with the old all-pairs definition, including the empty-family
convention.  This is an actual bridge, not a definition that assumes the
desired non-adjacent intersection conclusion. -/
theorem forestOfCopies_iff_empty_or_linkAllowed_joinTree_of_linear
    (E : Set (Set W)) (hLinear : LinearEdgeSet E)
    (hEdges : ∀ i, (F i).edges ⊆ E) :
    ForestOfCopies F ↔ IsEmpty ι ∨
      ∃ J : JoinTree F,
        ∀ ⦃i j⦄, J.tree.Adj i j → AllowedIntersection (F i) (F j) := by
  constructor
  · rintro ⟨hPair, hEmpty | hJ⟩
    · exact Or.inl hEmpty
    · obtain ⟨J⟩ := hJ
      exact Or.inr ⟨J, fun {_ _} hadj => hPair hadj.ne⟩
  · rintro (hEmpty | ⟨J, hLink⟩)
    · exact ⟨fun {i} => (hEmpty.false i).elim, Or.inl hEmpty⟩
    · exact J.forestOfCopies_of_linkAllowed_of_linear E hLinear hEdges hLink

end StructuralRamsey.Girth

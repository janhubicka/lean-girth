import Girth.CompactDiagramForest

/-!
# Binary forest gluing with a single retained-member link

The connector is an edge of the join tree on existing member labels.  It is
not an auxiliary singleton member.  Cross-side intersection hypotheses refer
to the two assembled unions; this permits a singleton point to be routed
through any member containing it, even when an intermediate outer owner has
no member containing that point.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I J : Type v} [Fintype I] [Fintype J]
variable {F : I → HypergraphPiece W} {G : J → HypergraphPiece W}

/-- Two genuine forests can be joined using only one allowed connector
intersection, provided those connectors contain every point shared across
the assembled sides.  All other cross-pair intersections are derived from
ambient linearity and running intersection. -/
theorem forestOfCopies_sumBridge_of_allowed_connectors_of_linear
    (hF : ForestOfCopies F) (hG : ForestOfCopies G)
    (E : Set (Set W)) (hLinear : LinearEdgeSet E)
    (hEdgesF : ∀ i, (F i).edges ⊆ E)
    (hEdgesG : ∀ j, (G j).edges ⊆ E)
    (i0 : I) (j0 : J)
    (hCross : ∀ (x : W) (i : I) (j : J),
      x ∈ (F i).carrier → x ∈ (G j).carrier →
        x ∈ (F i0).carrier ∧ x ∈ (G j0).carrier)
    (hConnector : AllowedIntersection (F i0) (G j0)) :
    ForestOfCopies (sumPieces F G) := by
  let : Nonempty I := ⟨i0⟩
  let : Nonempty J := ⟨j0⟩
  obtain ⟨JF⟩ := hF.joinTree_of_nonempty
  obtain ⟨JG⟩ := hG.joinTree_of_nonempty
  let K := JF.sumBridge JG i0 j0 hCross
  apply K.forestOfCopies_of_linkAllowed_of_linear E hLinear
  · intro s
    cases s with
    | inl i => exact hEdgesF i
    | inr j => exact hEdgesG j
  · intro a b hab
    change (JF.tree.sum JG.tree ⊔
      SimpleGraph.edge (Sum.inl i0) (Sum.inr j0)).Adj a b at hab
    cases a with
    | inl i =>
      cases b with
      | inl k =>
        have hAdj : JF.tree.Adj i k := by simpa [SimpleGraph.edge] using hab
        exact hF.pairwiseAllowed hAdj.ne
      | inr j =>
        have hEq : i = i0 ∧ j = j0 := by simpa [SimpleGraph.edge] using hab
        rcases hEq with ⟨rfl, rfl⟩
        exact hConnector
    | inr j =>
      cases b with
      | inl i =>
        have hEq : i = i0 ∧ j = j0 := by
          simpa [SimpleGraph.edge, and_comm] using hab
        rcases hEq with ⟨rfl, rfl⟩
        exact allowedIntersection_symm hConnector
      | inr k =>
        have hAdj : JG.tree.Adj j k := by simpa [SimpleGraph.edge] using hab
        exact hG.pairwiseAllowed hAdj.ne

/-- If the assembled sides share at most one point, choose connector members
containing that point on each side.  If they share no point, use arbitrary
members.  A singleton is only the intersection label of this link. -/
theorem forestOfCopies_sumPieces_of_subsingleton_union_overlap_of_linear
    [Nonempty I] [Nonempty J]
    (hF : ForestOfCopies F) (hG : ForestOfCopies G)
    (E : Set (Set W)) (hLinear : LinearEdgeSet E)
    (hEdgesF : ∀ i, (F i).edges ⊆ E)
    (hEdgesG : ∀ j, (G j).edges ⊆ E)
    (hSmall : ((⋃ i, (F i).carrier) ∩ (⋃ j, (G j).carrier)).Subsingleton) :
    ForestOfCopies (sumPieces F G) := by
  classical
  by_cases hSome : ((⋃ i, (F i).carrier) ∩ (⋃ j, (G j).carrier)).Nonempty
  · obtain ⟨x, hxF, hxG⟩ := hSome
    obtain ⟨i0, hxi⟩ := Set.mem_iUnion.mp hxF
    obtain ⟨j0, hxj⟩ := Set.mem_iUnion.mp hxG
    apply forestOfCopies_sumBridge_of_allowed_connectors_of_linear
      hF hG E hLinear hEdgesF hEdgesG i0 j0
    · intro y i j hyi hyj
      have hyx : y = x := hSmall
        ⟨Set.mem_iUnion.mpr ⟨i, hyi⟩, Set.mem_iUnion.mpr ⟨j, hyj⟩⟩ ⟨hxF, hxG⟩
      exact hyx ▸ ⟨hxi, hxj⟩
    · exact Or.inl (Set.Subsingleton.anti hSmall (fun y hy =>
        ⟨Set.mem_iUnion.mpr ⟨i0, hy.1⟩, Set.mem_iUnion.mpr ⟨j0, hy.2⟩⟩))
  · let i0 : I := Classical.choice inferInstance
    let j0 : J := Classical.choice inferInstance
    have hNo : ∀ (x : W) (i : I) (j : J),
        x ∈ (F i).carrier → x ∈ (G j).carrier → False := by
      intro x i j hxi hxj
      exact hSome ⟨x, Set.mem_iUnion.mpr ⟨i, hxi⟩, Set.mem_iUnion.mpr ⟨j, hxj⟩⟩
    apply forestOfCopies_sumBridge_of_allowed_connectors_of_linear
      hF hG E hLinear hEdgesF hEdgesG i0 j0
    · intro x i j hxi hxj
      exact (hNo x i j hxi hxj).elim
    · left
      intro x hx
      exact (hNo x i0 j0 hx.1 hx.2).elim

/-- A full-edge separator is carried by retained one-edge request members
on both sides.  It suffices to record their carrier and membership of that
edge; no assumptions on all other cross-side pairs are needed. -/
theorem forestOfCopies_sumPieces_of_common_edge_anchors_of_linear
    (hF : ForestOfCopies F) (hG : ForestOfCopies G)
    (E : Set (Set W)) (hLinear : LinearEdgeSet E)
    (hEdgesF : ∀ i, (F i).edges ⊆ E)
    (hEdgesG : ∀ j, (G j).edges ⊆ E)
    (i0 : I) (j0 : J) (e : Set W)
    (hFi : (F i0).carrier = e) (hGj : (G j0).carrier = e)
    (heFi : e ∈ (F i0).edges) (heGj : e ∈ (G j0).edges)
    (hOverlap : (⋃ i, (F i).carrier) ∩ (⋃ j, (G j).carrier) ⊆ e) :
    ForestOfCopies (sumPieces F G) := by
  apply forestOfCopies_sumBridge_of_allowed_connectors_of_linear
    hF hG E hLinear hEdgesF hEdgesG i0 j0
  · intro x i j hxi hxj
    have hxe := hOverlap
      ⟨Set.mem_iUnion.mpr ⟨i, hxi⟩, Set.mem_iUnion.mpr ⟨j, hxj⟩⟩
    exact ⟨hFi ▸ hxe, hGj ▸ hxe⟩
  · exact Or.inr ⟨e, heFi, heGj, by rw [hFi, hGj, Set.inter_self]⟩

end StructuralRamsey.Girth

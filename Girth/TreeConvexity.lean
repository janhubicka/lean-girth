import Girth.ForestTreeRewire

/-! # Convexity of connected induced subgraphs of a tree

A connected induced subgraph of a tree is geodesically convex: the unique
simple path between two of its vertices stays inside the induced set. This
is the graph-theoretic ingredient needed to preserve running intersections
when a join-tree vertex is rewired.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

/-- Every simple path in a tree between vertices of a preconnected induced
subgraph stays in that induced subgraph. -/
theorem SimpleGraph.IsTree.path_support_subset_of_induce_preconnected
    {G : SimpleGraph V}
    (hG : G.IsTree)
    {S : Set V}
    (hS : (G.induce S).Preconnected)
    {u w : V}
    (hu : u ∈ S) (hw : w ∈ S)
    (p : G.Walk u w)
    (hp : p.IsPath) :
    ∀ x ∈ p.support, x ∈ S := by
  let uS : S := ⟨u, hu⟩
  let wS : S := ⟨w, hw⟩
  have hreach : (G.induce S).Reachable uS wS := hS uS wS
  obtain ⟨q, hq⟩ := hreach.exists_isPath
  let inc : (G.induce S) →g G :=
    { toFun := fun z => z.1
      map_rel' := by
        intro a b hab
        exact hab }
  let qG : G.Walk u w := (q.map inc).copy rfl rfl
  have hqG : qG.IsPath := by
    dsimp [qG]
    exact (hq.map Subtype.val_injective).copy
  have hpq : p = qG := by
    exact congrArg Subtype.val
      (hG.isAcyclic.subsingleton_path u w |>.elim ⟨p, hp⟩ ⟨qG, hqG⟩)
  intro x hx
  rw [hpq] at hx
  dsimp [qG] at hx
  simp only [SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_map] at hx
  rcases List.mem_map.mp hx with ⟨z, hz, hzx⟩
  simpa [hzx] using z.2

/-- If two vertices lie in a set D, and an induced set S is preconnected
in a tree, then every path between the two vertices inside D can be lifted
to the intersection D ∩ S whenever both endpoints lie in S. -/
theorem SimpleGraph.IsTree.induce_inter_reachable
    {G : SimpleGraph V}
    (hG : G.IsTree)
    {D S : Set V}
    (hS : (G.induce S).Preconnected)
    (u w : D)
    (hu : u.1 ∈ S) (hw : w.1 ∈ S)
    (hreach : (G.induce D).Reachable u w) :
    ((G.induce D).induce {z : D | z.1 ∈ S}).Reachable
      ⟨u, hu⟩ ⟨w, hw⟩ := by
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  let incD : (G.induce D) →g G :=
    { toFun := fun z => z.1
      map_rel' := by
        intro a b hab
        exact hab }
  let pG : G.Walk u.1 w.1 := p.map incD
  have hpG : pG.IsPath := hp.map Subtype.val_injective
  have hstayG :
      ∀ x ∈ pG.support, x ∈ S :=
    hG.path_support_subset_of_induce_preconnected hS hu hw pG hpG
  have hstay :
      ∀ z ∈ p.support, z.1 ∈ S := by
    intro z hz
    apply hstayG z.1
    dsimp [pG]
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  exact (p.induce {z : D | z.1 ∈ S} hstay).reachable

end StructuralRamsey.Girth

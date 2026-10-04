import Girth.ForestLeafDeletion
import Girth.ForestSingleEdge

/-! # Geometry after deleting a join-tree member

The key observation for deleting a one-edge member is that any vertex shared
between two different components of the join tree after deletion must have
occurred in the deleted member.  This isolates the only possible cross-component
overlap before the one-edge intersection dichotomy is used.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

namespace JoinTree

/-- If two surviving pieces share a vertex but become unreachable after
deleting `center` from the join tree, then that shared vertex belongs to the
deleted piece. -/
theorem mem_center_of_shared_not_reachable_after_delete
    {F : ι → HypergraphPiece W}
    (J : JoinTree F)
    {center i j : ι}
    (hi : i ≠ center) (hj : j ≠ center)
    {x : W}
    (hxi : x ∈ (F i).carrier)
    (hxj : x ∈ (F j).carrier)
    (hnreach :
      ¬ (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        ⟨i, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩
        ⟨j, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hj⟩) :
    x ∈ (F center).carrier := by
  by_contra hxc
  let occ : Set ι := {k : ι | x ∈ (F k).carrier}
  let iOcc : occ := ⟨i, hxi⟩
  let jOcc : occ := ⟨j, hxj⟩
  have hreach :
      (J.tree.induce occ).Reachable iOcc jOcc := by
    simpa [occ, iOcc, jOcc] using J.running x iOcc jOcc
  let phi :
      (J.tree.induce occ) →g
        (J.tree.induce (({center} : Set ι)ᶜ)) :=
    { toFun := fun z =>
        ⟨z.1, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro hz
          subst hz
          exact hxc z.2⟩
      map_rel' := by
        intro a b hab
        exact hab }
  have hm := hreach.map phi
  apply hnreach
  convert hm using 1 <;> apply Subtype.ext <;> rfl

/-- Two neighbours of the deleted vertex cannot lie in the same component of
the deleted tree unless they are equal.  Thus every component of a tree with
one vertex removed has a unique attachment neighbour at that vertex. -/
theorem neighbor_eq_of_reachable_after_delete
    {F : ι → HypergraphPiece W}
    (J : JoinTree F)
    {center a b : ι}
    (ha : J.tree.Adj center a)
    (hb : J.tree.Adj center b)
    (hreach :
      (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        ⟨a, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
            using ha.ne.symm⟩
        ⟨b, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
            using hb.ne.symm⟩) :
    a = b := by
  obtain ⟨p0, hp0⟩ := hreach.exists_isPath
  let inc :
      (J.tree.induce (({center} : Set ι)ᶜ)) →g J.tree :=
    { toFun := fun z => z.1
      map_rel' := by
        intro u v huv
        exact huv }
  let p : J.tree.Walk a b := p0.map inc
  have hp : p.IsPath := by
    dsimp [p]
    exact hp0.map (fun u v h => Subtype.ext h)
  have hcenter : center ∉ p.support := by
    intro hc
    dsimp [p, inc] at hc
    rw [SimpleGraph.Walk.support_map] at hc
    rcases List.mem_map.mp hc with ⟨z, hz, hval⟩
    have hzout : z.1 ≠ center := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.2
    exact hzout hval
  let q : J.tree.Walk center b := p.cons ha
  have hq : q.IsPath := hp.cons hcenter
  have hbmem : b ∈ q.support := by
    simp [q]
  have heq : b = q.snd :=
    J.isTree.isAcyclic.eq_snd_of_adj_start hq hb hbmem
  have hsnd : q.snd = a := by
    simp [q]
  exact (heq.trans hsnd).symm

/-- If the deleted member is a one-edge piece and no surviving piece contains
that whole edge, then two pieces in different components after deletion meet in
at most one vertex.  Any two common vertices would both lie in the deleted edge,
contradicting the one-edge intersection dichotomy with either surviving piece. -/
theorem intersection_subsingleton_across_delete_of_oneEdge_of_no_full
    {F : ι → HypergraphPiece W}
    (J : JoinTree F)
    (hPair : PairwiseAllowed F)
    {center i j : ι}
    (hOne : (F center).IsOneEdge)
    (hi : i ≠ center) (hj : j ≠ center)
    (hNoFull :
      ∀ k : ι, k ≠ center →
        ¬ (F center).carrier ⊆ (F k).carrier)
    (hnreach :
      ¬ (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        ⟨i, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩
        ⟨j, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hj⟩) :
    ((F i).carrier ∩ (F j).carrier).Subsingleton := by
  intro x hx y hy
  have hxCenter : x ∈ (F center).carrier :=
    J.mem_center_of_shared_not_reachable_after_delete
      hi hj hx.1 hx.2 hnreach
  have hyCenter : y ∈ (F center).carrier :=
    J.mem_center_of_shared_not_reachable_after_delete
      hi hj hy.1 hy.2 hnreach
  have hCI :
      ((F center).carrier ∩ (F i).carrier).Subsingleton ∨
        (F center).carrier ⊆ (F i).carrier :=
    HypergraphPiece.isOneEdge_allowed_dichotomy
      hOne (hPair hi.symm)
  have hsmall :
      ((F center).carrier ∩ (F i).carrier).Subsingleton :=
    hCI.resolve_right (hNoFull i hi)
  exact hsmall ⟨hxCenter, hx.1⟩ ⟨hyCenter, hy.1⟩

end JoinTree

end StructuralRamsey.Girth

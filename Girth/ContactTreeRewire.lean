import Girth.ContactJoinTreeGlue
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Pure tree surgery extracted from the checked historical proof
at 99d26270. The underlying families are now sets, with no relational
piece, auxiliary-deletion or old forest induction dependency. -/

namespace StructuralRamsey.Girth
universe v
variable {W V ι : Type v}

namespace ContactJoinTree

/-- If two surviving pieces share a vertex but become unreachable after
deleting `center` from the join tree, then that shared vertex belongs to the
deleted piece. -/
theorem mem_center_of_shared_not_reachable_after_delete
    {F : ι → Set W}
    (J : ContactJoinTree F)
    {center i j : ι}
    (hi : i ≠ center) (hj : j ≠ center)
    {x : W}
    (hxi : x ∈ F i)
    (hxj : x ∈ F j)
    (hnreach :
      ¬ (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        ⟨i, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩
        ⟨j, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hj⟩) :
    x ∈ F center := by
  by_contra hxc
  let occ : Set ι := {k : ι | x ∈ F k}
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

/-- Every surviving vertex lies in a component with a neighbour of the
deleted vertex.  Equivalently, every component of a tree after deleting one
vertex has an attachment root adjacent to the deleted vertex. -/
theorem exists_neighbor_reachable_after_delete
    {F : ι → Set W}
    (J : ContactJoinTree F)
    {center i : ι}
    (hi : i ≠ center) :
    ∃ root : ι, ∃ hroot : J.tree.Adj center root,
      (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        ⟨root, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
            using hroot.ne.symm⟩
        ⟨i, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩ := by
  obtain ⟨p, hp, _huniq⟩ :=
    J.isTree.existsUnique_path center i
  have hnp : ¬ p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne hi.symm
  let root : ι := p.snd
  have hroot : J.tree.Adj center root := by
    exact p.adj_snd hnp
  have hcenterTail : center ∉ p.tail.support := by
    rw [p.support_tail_of_not_nil hnp]
    have hnodup : (center :: p.support.tail).Nodup := by
      rw [p.cons_tail_support]
      exact hp.support_nodup
    exact (List.nodup_cons.mp hnodup).1
  have htail :
      ∀ x ∈ p.tail.support, x ∈ (({center} : Set ι)ᶜ) := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    subst x
    exact hcenterTail hx
  let q :=
    p.tail.induce (({center} : Set ι)ᶜ) htail
  refine ⟨root, hroot, ?_⟩
  have hq := q.reachable
  convert hq using 1 <;> apply Subtype.ext <;> rfl

/-- Two neighbours of the deleted vertex cannot lie in the same component of
the deleted tree unless they are equal.  Thus every component of a tree with
one vertex removed has a unique attachment neighbour at that vertex. -/
theorem neighbor_eq_of_reachable_after_delete
    {F : ι → Set W}
    (J : ContactJoinTree F)
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

/-- Let `root` be the neighbour through which a component attaches to the
deleted vertex.  Any vertex shared by the deleted member and a piece in that
component already belongs to the root piece.  This is the running-intersection
form of the manuscript's "components attached through the same vertex" step. -/
theorem mem_root_of_mem_center_and_reachable_after_delete
    {F : ι → Set W}
    (J : ContactJoinTree F)
    {center root i : ι}
    (hroot : J.tree.Adj center root)
    (hi : i ≠ center)
    (hreach :
      (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        ⟨root, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
            using hroot.ne.symm⟩
        ⟨i, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
            using hi⟩)
    {x : W}
    (hxCenter : x ∈ F center)
    (hxI : x ∈ F i) :
    x ∈ F root := by
  obtain ⟨p0, hp0⟩ := hreach.exists_isPath
  let delInc :
      (J.tree.induce (({center} : Set ι)ᶜ)) →g J.tree :=
    { toFun := fun z => z.1
      map_rel' := by
        intro u v huv
        exact huv }
  let p : J.tree.Walk root i := p0.map delInc
  have hp : p.IsPath := by
    dsimp [p]
    exact hp0.map (fun u v h => Subtype.ext h)
  have hcenter : center ∉ p.support := by
    intro hc
    dsimp [p, delInc] at hc
    rw [SimpleGraph.Walk.support_map] at hc
    rcases List.mem_map.mp hc with ⟨z, hz, hval⟩
    have hzout : z.1 ≠ center := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.2
    exact hzout hval
  let q : J.tree.Walk center i := p.cons hroot
  have hq : q.IsPath := hp.cons hcenter

  let occ : Set ι := {k : ι | x ∈ F k}
  let centerOcc : occ := ⟨center, hxCenter⟩
  let iOcc : occ := ⟨i, hxI⟩
  obtain ⟨r0, hr0⟩ :=
    (J.running x centerOcc iOcc).exists_isPath
  let occInc : (J.tree.induce occ) →g J.tree :=
    { toFun := fun z => z.1
      map_rel' := by
        intro u v huv
        exact huv }
  let r : J.tree.Walk center i := r0.map occInc
  have hr : r.IsPath := by
    dsimp [r]
    exact hr0.map (fun u v h => Subtype.ext h)
  have hqr : q = r :=
    (J.isTree.existsUnique_path center i).unique hq hr
  have hrootEq : root = r.snd := by
    calc
      root = q.snd := by simp [q]
      _ = r.snd := congrArg SimpleGraph.Walk.snd hqr
  have hrsndVal : r.snd = r0.snd.1 := by
    change (r0.map occInc).getVert 1 = (r0.getVert 1).1
    rw [SimpleGraph.Walk.getVert_map]
    rfl
  have hrsnd : x ∈ F r.snd := by
    rw [hrsndVal]
    exact r0.snd.2
  rw [← hrootEq] at hrsnd
  exact hrsnd

/-- A vertex shared by pieces in two different post-deletion components is
visible at both component roots.  Thus all cross-component overlap can be
represented solely at the roots when the deleted node is replaced. -/
theorem shared_mem_component_roots
    {F : ι → Set W}
    (J : ContactJoinTree F)
    {center root₁ root₂ i j : ι}
    (hroot₁ : J.tree.Adj center root₁)
    (hroot₂ : J.tree.Adj center root₂)
    (hi : i ≠ center)
    (hj : j ≠ center)
    (hreach₁ :
      (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        ⟨root₁, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
            using hroot₁.ne.symm⟩
        ⟨i, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩)
    (hreach₂ :
      (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        ⟨root₂, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
            using hroot₂.ne.symm⟩
        ⟨j, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hj⟩)
    (hnreach :
      ¬ (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        ⟨i, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩
        ⟨j, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hj⟩)
    {x : W}
    (hxi : x ∈ F i)
    (hxj : x ∈ F j) :
    x ∈ F root₁ ∩ F root₂ := by
  have hxCenter : x ∈ F center :=
    J.mem_center_of_shared_not_reachable_after_delete
      hi hj hxi hxj hnreach
  exact
    ⟨J.mem_root_of_mem_center_and_reachable_after_delete
        hroot₁ hi hreach₁ hxCenter hxi,
      J.mem_root_of_mem_center_and_reachable_after_delete
        hroot₂ hj hreach₂ hxCenter hxj⟩


end ContactJoinTree

/-- A neighbour of the deleted vertex, viewed as a surviving vertex. -/
def ContactJoinTree.neighborToErasedEmbedding
    {F : ι → Set V}
    (J : ContactJoinTree F) (center : ι) :
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
def ContactJoinTree.rewireAfterDelete
    {F : ι → Set V}
    (J : ContactJoinTree F) (center : ι)
    (R : SimpleGraph (J.tree.neighborSet center)) :
    SimpleGraph {i : ι // i ∈ ({center} : Set ι)ᶜ} :=
  J.tree.induce (({center} : Set ι)ᶜ) ⊔
    R.map (J.neighborToErasedEmbedding center)

/-- Edges inserted between former neighbours of the deleted centre are new:
two distinct neighbours of a vertex in a tree cannot already lie in the same
component after deleting that vertex. -/
theorem ContactJoinTree.disjoint_deletedGraph_map_neighborGraph
    {F : ι → Set V} [Fintype ι]
    (J : ContactJoinTree F) (center : ι)
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
theorem ContactJoinTree.reachable_occurrence_after_delete_of_not_mem_center
    {F : ι → Set V}
    (J : ContactJoinTree F)
    {center i j : ι}
    (hi : i ≠ center) (hj : j ≠ center)
    {x : V}
    (hxi : x ∈ F i)
    (hxj : x ∈ F j)
    (hxCenter : x ∉ F center) :
    ((J.tree.induce (({center} : Set ι)ᶜ)).induce
      {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ F k.1}).Reachable
        ⟨⟨i, by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩,
          hxi⟩
        ⟨⟨j, by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hj⟩,
          hxj⟩ := by
  let occ : Set ι := {k : ι | x ∈ F k}
  let iOcc : occ := ⟨i, hxi⟩
  let jOcc : occ := ⟨j, hxj⟩
  let phi :
      (J.tree.induce occ) →g
        ((J.tree.induce (({center} : Set ι)ᶜ)).induce
          {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ F k.1}) :=
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
theorem ContactJoinTree.reachable_occurrence_after_delete
    {F : ι → Set V}
    (J : ContactJoinTree F)
    {center i j : ι}
    (hi : i ≠ center) (hj : j ≠ center)
    {x : V}
    (hxi : x ∈ F i)
    (hxj : x ∈ F j)
    (hdel :
      (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        ⟨i, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩
        ⟨j, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hj⟩) :
    ((J.tree.induce (({center} : Set ι)ᶜ)).induce
      {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ F k.1}).Reachable
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

  let occ : Set ι := {k : ι | x ∈ F k}
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
      ∀ z ∈ q0.support, x ∈ F z.1 := by
    intro z hz
    have hzq : z.1 ∈ q.support := by
      dsimp [q, delInc]
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨z, hz, rfl⟩
    rw [← hpq] at hzq
    dsimp [p, occInc] at hzq
    rw [SimpleGraph.Walk.support_map] at hzq
    rcases List.mem_map.mp hzq with ⟨w, hw, hwval⟩
    have hwx : x ∈ F w.1 := w.2
    change w.1 = z.1 at hwval
    rw [← hwval]
    exact hwx
  let qx := q0.induce {k : {t : ι // t ∈ (({center} : Set ι)ᶜ)} |
        x ∈ F k.1} hqX
  have hqx := qx.reachable
  convert hqx using 1 <;> apply Subtype.ext <;> apply Subtype.ext <;> rfl

end StructuralRamsey.Girth

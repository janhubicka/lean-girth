import Girth.ContactBadCycle
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Pure join-tree API, extracted from the old checked ForestEnumeration
and ForestLeafDeletion modules. No relational support or old cycle-word
proof is imported.  A join tree is here a tree of arbitrary sets. -/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

structure ContactJoinTree (F : ι → Set W) where
  tree : SimpleGraph ι
  isTree : tree.IsTree
  running : ∀ x : W, (tree.induce {i : ι | x ∈ F i}).Preconnected


/-- If `leaf` has unique neighbour `parent` in a join tree, then every
ambient vertex shared by `leaf` and any other piece also belongs to
`parent`. -/
theorem ContactJoinTree.mem_parent_of_mem_leaf_and_other
    {F : ι → Set W} (J : ContactJoinTree F)
    {leaf parent other : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent)
    (hne : other ≠ leaf)
    {x : W}
    (hxLeaf : x ∈ F leaf)
    (hxOther : x ∈ F other) :
    x ∈ F parent := by
  let leafOcc : {k : ι | x ∈ F k} := ⟨leaf, hxLeaf⟩
  let otherOcc : {k : ι | x ∈ F k} := ⟨other, hxOther⟩
  have hOccNe : leafOcc ≠ otherOcc := by
    intro h
    apply hne
    exact congrArg Subtype.val h |>.symm
  obtain ⟨p, hp⟩ := (J.running x leafOcc otherOcc).exists_isPath
  have hnon : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hOccNe
  have hfirst :
      (J.tree.induce {k : ι | x ∈ F k}).Adj leafOcc p.snd :=
    p.adj_snd hnon
  have hfirst' : J.tree.Adj leaf p.snd.1 := by
    exact hfirst
  have hsnd : p.snd.1 = parent := huniq p.snd.1 hfirst'
  simpa [hsnd] using p.snd.2

/-- A leaf carrier meets the union of all other carriers exactly in its
intersection with the unique neighbouring piece. -/
theorem ContactJoinTree.leaf_inter_iUnion_eq_parent
    {F : ι → Set W} (J : ContactJoinTree F)
    {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent) :
    F leaf ∩
        (⋃ j : {j : ι // j ≠ leaf}, F j.1) =
      F leaf ∩ F parent := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases Set.mem_iUnion.mp hx.2 with ⟨j, hxj⟩
    exact ⟨hx.1,
      J.mem_parent_of_mem_leaf_and_other hadj huniq j.2 hx.1 hxj⟩
  · intro x hx
    refine ⟨hx.1, Set.mem_iUnion.mpr ?_⟩
    have hpne : parent ≠ leaf := hadj.ne.symm
    exact ⟨⟨parent, hpne⟩, hx.2⟩


/-- Every nontrivial finite join tree has a leaf whose intersection with all
remaining carriers is exactly its intersection with its unique neighbour. -/
theorem ContactJoinTree.exists_leaf_attachment
    {F : ι → Set W} [Fintype ι] [Nontrivial ι]
    (J : ContactJoinTree F) :
    ∃ leaf parent : ι,
      J.tree.Adj leaf parent ∧
      (∀ j : ι, J.tree.Adj leaf j → j = parent) ∧
      F leaf ∩
          (⋃ j : {j : ι // j ≠ leaf}, F j.1) =
        F leaf ∩ F parent := by
  classical
  obtain ⟨leaf, hdeg⟩ :=
    J.isTree.exists_vert_degree_one_of_nontrivial
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hdeg
  rcases hdeg with ⟨parent, hadj, huniq⟩
  refine ⟨leaf, parent, hadj, huniq, ?_⟩
  exact J.leaf_inter_iUnion_eq_parent hadj huniq




/-- Restrict a family of pieces to all indices different from `leaf`. -/
def contactEraseSet
    (F : ι → Set W) (leaf : ι) :
    {i : ι // i ∈ (({leaf} : Set ι)ᶜ)} → Set W :=
  fun i => F i.1

namespace ContactJoinTree

/-- A leaf with a specified unique neighbour has graph-theoretic degree one. -/
theorem degree_eq_one_of_unique_neighbor
    {F : ι → Set W} [Fintype ι]
    (J : ContactJoinTree F) {leaf parent : ι}
    [Fintype (J.tree.neighborSet leaf)]
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent) :
    J.tree.degree leaf = 1 := by
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  exact ⟨parent, hadj, huniq⟩

/-- Deleting a leaf from a finite join tree leaves a join tree on the remaining
pieces.  This is the join-tree deletion step used in the manuscript's
one-A-copy elimination and subsequent leaf inductions. -/
noncomputable def eraseLeaf
    {F : ι → Set W} [Fintype ι]
    (J : ContactJoinTree F) {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent) :
    ContactJoinTree (contactEraseSet F leaf) := by
  classical
  letI : Fintype (J.tree.neighborSet leaf) :=
    Fintype.ofInjective (fun z : J.tree.neighborSet leaf => z.1)
      Subtype.val_injective
  have hdeg : J.tree.degree leaf = 1 :=
    J.degree_eq_one_of_unique_neighbor hadj huniq
  have hTreeErase :
      (J.tree.induce (({leaf} : Set ι)ᶜ)).IsTree := by
    constructor
    · exact J.isTree.connected.induce_compl_singleton_of_degree_eq_one hdeg
    · exact J.isTree.isAcyclic.induce (({leaf} : Set ι)ᶜ)
  refine
    { tree := J.tree.induce (({leaf} : Set ι)ᶜ)
      isTree := hTreeErase
      running := ?_ }
  intro x
  let occ : Set ι := {i : ι | x ∈ F i}
  let occErase :
      Set {i : ι // i ∈ (({leaf} : Set ι)ᶜ)} :=
    {i | x ∈ F i.1}
  change
    ((J.tree.induce (({leaf} : Set ι)ᶜ)).induce occErase).Preconnected
  by_cases hxLeaf : x ∈ F leaf
  · let leafOcc : occ := ⟨leaf, hxLeaf⟩
    by_cases hsub : occErase.Subsingleton
    · letI : Subsingleton occErase := hsub.coe_sort
      exact SimpleGraph.Preconnected.of_subsingleton
    · have hnontriv : occErase.Nontrivial :=
        Set.not_subsingleton_iff.mp hsub
      have hparentOcc : x ∈ F parent := by
        obtain ⟨j, hj, _k, _hk, _hjk⟩ := hnontriv
        have hjne : j.1 ≠ leaf := by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using j.2
        exact
          J.mem_parent_of_mem_leaf_and_other
            hadj huniq hjne hxLeaf hj
      let parentOcc : occ := ⟨parent, hparentOcc⟩
      have hOccPre : (J.tree.induce occ).Preconnected := by
        simpa [occ] using J.running x
      letI : Nonempty occ := ⟨leafOcc⟩
      have hOccConnected : (J.tree.induce occ).Connected :=
        ⟨hOccPre⟩
      letI : Fintype occ :=
        Fintype.ofInjective (fun z : occ => z.1) Subtype.val_injective
      letI : Fintype ((J.tree.induce occ).neighborSet leafOcc) :=
        Fintype.ofInjective
          (fun z : (J.tree.induce occ).neighborSet leafOcc => z.1)
          Subtype.val_injective
      have hLeafDegree :
          (J.tree.induce occ).degree leafOcc = 1 := by
        rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
        refine ⟨parentOcc, ?_, ?_⟩
        · exact hadj
        · intro q hq
          apply Subtype.ext
          exact huniq q.1 hq
      have hDeleted :
          ((J.tree.induce occ).induce ({leafOcc} : Set occ)ᶜ).Preconnected :=
        (hOccConnected.induce_compl_singleton_of_degree_eq_one
          hLeafDegree).preconnected
      let phi :
          ((J.tree.induce occ).induce ({leafOcc} : Set occ)ᶜ) →g
            ((J.tree.induce (({leaf} : Set ι)ᶜ)).induce occErase) :=
        { toFun := fun z =>
            ⟨⟨z.1.1, by
                have hz : z.1 ≠ leafOcc := by
                  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.2
                have hne : z.1.1 ≠ leaf := by
                  intro h
                  apply hz
                  apply Subtype.ext
                  exact h
                simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne⟩,
              z.1.2⟩
          map_rel' := by
            intro a b hab
            exact hab }
      have hphi : Function.Surjective phi := by
        intro y
        let q : occ := ⟨y.1.1, y.2⟩
        have hqne : q ≠ leafOcc := by
          have hyne : y.1.1 ≠ leaf := by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y.1.2
          intro h
          apply hyne
          exact congrArg Subtype.val h
        refine ⟨⟨q, ?_⟩, ?_⟩
        · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hqne
        · apply Subtype.ext
          apply Subtype.ext
          rfl
      exact hDeleted.map phi hphi
  · have hOld : (J.tree.induce occ).Preconnected := by
      simpa [occ] using J.running x
    let phi :
        (J.tree.induce occ) →g
          ((J.tree.induce (({leaf} : Set ι)ᶜ)).induce occErase) :=
      { toFun := fun z =>
          ⟨⟨z.1, by
              have hne : z.1 ≠ leaf := by
                intro h
                subst h
                exact hxLeaf z.2
              simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne⟩,
            z.2⟩
        map_rel' := by
          intro a b hab
          exact hab }
    have hphi : Function.Surjective phi := by
      intro y
      refine ⟨⟨y.1.1, y.2⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rfl
    exact hOld.map phi hphi


end ContactJoinTree
end StructuralRamsey.Girth

import Girth.ForestEnumeration

/-! # Deleting leaves from join trees

This is the first inductive operation needed for the manuscript's
forest-to-supported-tree observation.  Deleting a leaf of a join tree leaves a
join tree on the remaining pieces.  The only point requiring care is the
running-intersection condition: for each ambient vertex, deleting a global
leaf cannot disconnect its occurrence subtree.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Restrict a family of pieces to all indices different from `leaf`.  The
complement-of-singleton subtype is chosen so that the restricted join tree is
literally `SimpleGraph.induce`. -/
def erasePiece
    (F : ι → HypergraphPiece W) (leaf : ι) :
    (({leaf} : Set ι)ᶜ) → HypergraphPiece W :=
  fun i => F i.1

namespace JoinTree

/-- A leaf with a specified unique neighbour has graph-theoretic degree one. -/
theorem degree_eq_one_of_unique_neighbor
    {F : ι → HypergraphPiece W} [Fintype ι]
    (J : JoinTree F) {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent) :
    J.tree.degree leaf = 1 := by
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  exact ⟨parent, hadj, huniq⟩

/-- Deleting a leaf from a finite join tree leaves a join tree on the remaining
pieces.  This is the join-tree deletion step used in the manuscript's
one-A-copy elimination and subsequent leaf inductions. -/
noncomputable def eraseLeaf
    {F : ι → HypergraphPiece W} [Fintype ι]
    (J : JoinTree F) {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent) :
    JoinTree (erasePiece F leaf) := by
  classical
  let s : Set ι := ({leaf} : Set ι)ᶜ
  have hdeg : J.tree.degree leaf = 1 :=
    J.degree_eq_one_of_unique_neighbor hadj huniq
  have hTreeErase : (J.tree.induce s).IsTree := by
    constructor
    · simpa [s] using
        J.isTree.connected.induce_compl_singleton_of_degree_eq_one hdeg
    · exact J.isTree.isAcyclic.induce s
  refine
    { tree := J.tree.induce s
      isTree := hTreeErase
      running := ?_ }
  intro x
  let occ : Set ι := {i : ι | x ∈ (F i).carrier}
  let occErase : Set s := {i : s | x ∈ (F i.1).carrier}
  change
    ((J.tree.induce s).induce occErase).Preconnected
  by_cases hxLeaf : x ∈ (F leaf).carrier
  · let leafOcc : occ := ⟨leaf, hxLeaf⟩
    by_cases hsub : occErase.Subsingleton
    · letI : Subsingleton occErase := hsub
      exact SimpleGraph.Preconnected.of_subsingleton
    · have hneOcc : Nontrivial occErase :=
        not_subsingleton_iff_nontrivial.mp
          (by
            intro h
            exact hsub h)
      letI : Nontrivial occErase := hneOcc
      have hparentOcc : x ∈ (F parent).carrier := by
        obtain ⟨j, k, hj, hk, hjk⟩ :=
          Set.not_subsingleton_iff.mp (by
            simpa [not_subsingleton_iff_nontrivial] using hneOcc)
        have hjne : j.1 ≠ leaf := by
          simpa [s] using j.2
        exact
          J.mem_parent_of_mem_leaf_and_other
            hadj huniq hjne hxLeaf j.2
      let parentOcc : occ := ⟨parent, hparentOcc⟩
      have hOccConnected : (J.tree.induce occ).Connected := by
        refine ⟨?_, ⟨leafOcc⟩⟩
        simpa [occ] using J.running x
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
            ((J.tree.induce s).induce occErase) where
        toFun z :=
          ⟨⟨z.1.1, by
              change z.1.1 ≠ leaf
              intro h
              apply z.2
              apply Subtype.ext
              exact h⟩,
            z.1.2⟩
        map_rel' := by
          intro a b hab
          exact hab
      have hphi : Function.Surjective phi := by
        intro y
        let q : occ := ⟨y.1.1, y.2⟩
        have hqne : q ≠ leafOcc := by
          intro h
          have hv : y.1.1 = leaf :=
            congrArg Subtype.val h
          exact y.1.2 (by simpa [s] using hv)
        refine ⟨⟨q, ?_⟩, ?_⟩
        · simpa using hqne
        · apply Subtype.ext
          apply Subtype.ext
          rfl
      exact hDeleted.map phi hphi
  · have hOld : (J.tree.induce occ).Preconnected := by
      simpa [occ] using J.running x
    let phi :
        (J.tree.induce occ) →g
          ((J.tree.induce s).induce occErase) where
      toFun z :=
        ⟨⟨z.1, by
            change z.1 ≠ leaf
            intro h
            subst h
            exact hxLeaf z.2⟩,
          z.2⟩
      map_rel' := by
        intro a b hab
        exact hab
    have hphi : Function.Surjective phi := by
      intro y
      refine ⟨⟨y.1.1, y.2⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rfl
    exact hOld.map phi hphi

/-- Pairwise allowed intersections are inherited after deleting a member. -/
theorem pairwiseAllowed_erase
    {F : ι → HypergraphPiece W}
    (h : PairwiseAllowed F) (leaf : ι) :
    PairwiseAllowed (erasePiece F leaf) := by
  intro i j hij
  apply h
  intro hval
  apply hij
  apply Subtype.ext
  exact hval

end JoinTree

/-- Hence deleting a graph-theoretic leaf from a finite forest leaves a
forest, with the empty remaining family covered by the manuscript's explicit
empty-family convention. -/
theorem ForestOfCopies.erase_leaf
    {F : ι → HypergraphPiece W} [Fintype ι]
    (hF : ForestOfCopies F)
    (J : JoinTree F)
    {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent) :
    ForestOfCopies (erasePiece F leaf) := by
  refine ⟨JoinTree.pairwiseAllowed_erase hF.pairwiseAllowed leaf, ?_⟩
  by_cases hne : Nonempty (({leaf} : Set ι)ᶜ)
  · exact Or.inr ⟨J.eraseLeaf hadj huniq⟩
  · have hEmpty : IsEmpty (({leaf} : Set ι)ᶜ) := by
      exact not_nonempty_iff.mp hne
    exact Or.inl hEmpty

end StructuralRamsey.Girth

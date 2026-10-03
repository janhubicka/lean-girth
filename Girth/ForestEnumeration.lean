import Girth.Forest

/-! # Leaf attachments in join trees

The manuscript repeatedly uses the rooted-enumeration consequence of a join
tree.  The essential local fact is simpler: a leaf piece meets the union of
all remaining pieces exactly where it meets its unique neighbour.  This file
packages that fact so later forest deletion and lifting proofs can proceed by
leaf induction rather than by repeated path arguments.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- If `leaf` has unique neighbour `parent` in a join tree, then every
ambient vertex shared by `leaf` and any other piece also belongs to
`parent`. -/
theorem JoinTree.mem_parent_of_mem_leaf_and_other
    {F : ι → HypergraphPiece W} (J : JoinTree F)
    {leaf parent other : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent)
    (hne : other ≠ leaf)
    {x : W}
    (hxLeaf : x ∈ (F leaf).carrier)
    (hxOther : x ∈ (F other).carrier) :
    x ∈ (F parent).carrier := by
  let leafOcc : {k : ι | x ∈ (F k).carrier} := ⟨leaf, hxLeaf⟩
  let otherOcc : {k : ι | x ∈ (F k).carrier} := ⟨other, hxOther⟩
  have hOccNe : leafOcc ≠ otherOcc := by
    intro h
    apply hne
    exact congrArg Subtype.val h |>.symm
  obtain ⟨p, hp⟩ := (J.running x leafOcc otherOcc).exists_isPath
  have hnon : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hOccNe
  have hfirst :
      (J.tree.induce {k : ι | x ∈ (F k).carrier}).Adj leafOcc p.snd :=
    p.adj_snd hnon
  have hfirst' : J.tree.Adj leaf p.snd.1 := by
    exact hfirst
  have hsnd : p.snd.1 = parent := huniq p.snd.1 hfirst'
  simpa [hsnd] using p.snd.2

/-- A leaf carrier meets the union of all other carriers exactly in its
intersection with the unique neighbouring piece. -/
theorem JoinTree.leaf_inter_iUnion_eq_parent
    {F : ι → HypergraphPiece W} (J : JoinTree F)
    {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent) :
    (F leaf).carrier ∩
        (⋃ j : {j : ι // j ≠ leaf}, (F j.1).carrier) =
      (F leaf).carrier ∩ (F parent).carrier := by
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
theorem JoinTree.exists_leaf_attachment
    {F : ι → HypergraphPiece W} [Fintype ι] [Nontrivial ι]
    (J : JoinTree F) :
    ∃ leaf parent : ι,
      J.tree.Adj leaf parent ∧
      (∀ j : ι, J.tree.Adj leaf j → j = parent) ∧
      (F leaf).carrier ∩
          (⋃ j : {j : ι // j ≠ leaf}, (F j.1).carrier) =
        (F leaf).carrier ∩ (F parent).carrier := by
  classical
  obtain ⟨leaf, hdeg⟩ :=
    J.isTree.exists_vert_degree_one_of_nontrivial
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hdeg
  rcases hdeg with ⟨parent, hadj, huniq⟩
  refine ⟨leaf, parent, hadj, huniq, ?_⟩
  exact J.leaf_inter_iUnion_eq_parent hadj huniq

end StructuralRamsey.Girth

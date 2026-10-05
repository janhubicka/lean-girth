import Girth.Forest

/-! # Lifting support join trees to full carriers

A join tree is often first obtained for support hypergraphs.  If every vertex
shared by two full members is already visible in the support carrier of each
incident member, the same tree also has the running-intersection property for
the full member carriers.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Every vertex shared by two distinct full members is visible in both of
their support carriers. -/
def SharedVerticesVisible
    (F : ι → HypergraphPiece W) (full : ι → Set W) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → ∀ ⦃x : W⦄,
    x ∈ full i → x ∈ full j →
      x ∈ (F i).carrier ∧ x ∈ (F j).carrier

/-- Enlarge the carrier of a hypergraph piece without changing its support
edges. -/
def HypergraphPiece.enlargeCarrier
    (F : HypergraphPiece W) (C : Set W)
    (h : F.carrier ⊆ C) : HypergraphPiece W where
  carrier := C
  edges := F.edges
  edge_subset_carrier := by
    intro e he
    exact Set.Subset.trans (F.edge_subset he) h

/-- Under shared-vertex visibility, the running-intersection property of a
support join tree lifts to the full member carriers. -/
theorem JoinTree.fullOccurrence_preconnected
    {F : ι → HypergraphPiece W}
    (J : JoinTree F)
    (full : ι → Set W)
    (hSub : ∀ i, (F i).carrier ⊆ full i)
    (hVisible : SharedVerticesVisible F full)
    (x : W) :
    (J.tree.induce {i : ι | x ∈ full i}).Preconnected := by
  intro a b
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.refl _
  have hij : a.1 ≠ b.1 := by
    intro h
    apply hab
    exact Subtype.ext h
  have hsupp :
      x ∈ (F a.1).carrier ∧ x ∈ (F b.1).carrier :=
    hVisible hij a.2 b.2
  let aS : {i : ι | x ∈ (F i).carrier} := ⟨a.1, hsupp.1⟩
  let bS : {i : ι | x ∈ (F i).carrier} := ⟨b.1, hsupp.2⟩
  have hreach :
      (J.tree.induce {i : ι | x ∈ (F i).carrier}).Reachable aS bS :=
    J.running x aS bS
  let phi :
      (J.tree.induce {i : ι | x ∈ (F i).carrier}) →g
        (J.tree.induce {i : ι | x ∈ full i}) :=
    { toFun := fun z => ⟨z.1, hSub z.1 z.2⟩
      map_rel' := by
        intro u v huv
        exact huv }
  have hm := hreach.map phi
  convert hm using 1 <;> apply Subtype.ext <;> rfl

/-- Enlarge all support carriers in a join tree.  The tree itself is
unchanged. -/
def JoinTree.enlargeCarriers
    {F : ι → HypergraphPiece W}
    (J : JoinTree F)
    (full : ι → Set W)
    (hSub : ∀ i, (F i).carrier ⊆ full i)
    (hVisible : SharedVerticesVisible F full) :
    JoinTree (fun i => (F i).enlargeCarrier (full i) (hSub i)) where
  tree := J.tree
  isTree := J.isTree
  running := by
    intro x
    simpa [HypergraphPiece.enlargeCarrier] using
      J.fullOccurrence_preconnected full hSub hVisible x

end StructuralRamsey.Girth

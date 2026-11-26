import Girth.ContactJoinTreeGlue

/-! Constructive inverse operations for the usual join-tree
elimination argument. A private vertex can be restored without
changing the tree. A piece whose shared trace is contained in one
remaining piece can be restored as a leaf. These are the construction
steps of the chordal/conformal converse, not a proof of the existence
of an elimination order. -/

namespace StructuralRamsey.Girth
universe v
variable {W I : Type v}

namespace ContactJoinTree

/-- A one-member family has a join tree. -/
def of_subsingleton [Subsingleton I] [Nonempty I]
    (F : I → Set W) : ContactJoinTree F where
  tree := ⊥
  isTree := by
    constructor
    · exact ⟨SimpleGraph.Preconnected.of_subsingleton⟩
    · exact SimpleGraph.isAcyclic_bot
  running := fun _ => SimpleGraph.Preconnected.of_subsingleton

/-- Restoring a vertex occurring in at most one member does not
affect running intersections at any other vertex. -/
def restorePrivate {F : I → Set W} (x : W)
    (J : ContactJoinTree (fun i => F i \ {x}))
    (hpriv : {i : I | x ∈ F i}.Subsingleton) : ContactJoinTree F where
  tree := J.tree
  isTree := J.isTree
  running := by
    intro y
    by_cases he : y = x
    · subst y
      letI : Subsingleton {i : I | x ∈ F i} := hpriv.coe_sort
      exact SimpleGraph.Preconnected.of_subsingleton
    · have hsets : {i : I | y ∈ F i \ {x}} = {i : I | y ∈ F i} := by
        ext i
        simp [he]
      have h := J.running y
      change (J.tree.induce {i : I | y ∈ F i \ {x}}).Preconnected at h
      rw [hsets] at h
      exact h

/-- Split the index type into one distinguished member and its
complement. This is an actual bijective relabelling. -/
noncomputable def singletonSumCompl (a : I) :
    PUnit.{v+1} ⊕ {i : I // i ∈ ({a} : Set I)ᶜ} ≃ I := by
  classical
  refine {
    toFun := fun x => match x with | .inl _ => a | .inr b => b.val
    invFun := fun x => if h : x = a then .inl PUnit.unit else .inr ⟨x,by
      simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using h⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro x
    cases x with
    | inl p =>
      cases p
      simp
    | inr b =>
      have hn : b.val ≠ a := by
        simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using b.property
      simp [hn]
  · intro x
    by_cases he : x = a <;> simp [he]

/-- Add a leaf whose intersection with the union of the other
carriers is contained in a specified parent carrier. -/
noncomputable def attachLeaf [Fintype I] {F : I → Set W}
    (a b : I) (hab : b ≠ a)
    (J : ContactJoinTree (contactEraseSet F a))
    (htrace : ∀ x ∈ F a, ∀ i : I, i ≠ a → x ∈ F i → x ∈ F b) :
    ContactJoinTree F := by
  classical
  let L := {i : I // i ∈ ({a} : Set I)ᶜ}
  let b' : L := ⟨b,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hab⟩
  letI : Fintype L := Fintype.ofFinite L
  let F₁ : PUnit.{v+1} → Set W := fun _ => F a
  let J₁ := ContactJoinTree.of_subsingleton F₁
  have hcross : ∀ (x : W) (i : PUnit.{v+1}) (j : L),
      x ∈ F₁ i → x ∈ contactEraseSet F a j →
      x ∈ F₁ PUnit.unit ∧ x ∈ contactEraseSet F a b' := by
    intro x i j hx hj
    have hn : j.val ≠ a := by
      simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using j.property
    exact ⟨hx,htrace x hx j.val hn hj⟩
  let T := J₁.sumBridge J PUnit.unit b' hcross
  let e := singletonSumCompl a
  have hf : contactSumSets F₁ (contactEraseSet F a) = F ∘ e := by
    funext j
    cases j <;> rfl
  have htree : ContactJoinTree (F ∘ e) := hf ▸ T
  have hnew := htree.reindex e.symm
  have he : (fun k => (F ∘ e) (e.symm k)) = F := by
    funext k
    exact congrArg F (e.apply_symm_apply k)
  exact he ▸ hnew

/-- A contained member is a special case of leaf restoration. -/
noncomputable def restoreContained [Fintype I] {F : I → Set W}
    (a b : I) (hab : b ≠ a)
    (J : ContactJoinTree (contactEraseSet F a))
    (hsub : F a ⊆ F b) : ContactJoinTree F :=
  attachLeaf a b hab J (fun x hx _ _ _ => hsub hx)

end ContactJoinTree
end StructuralRamsey.Girth

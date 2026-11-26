import Girth.ContactMinimumCompletion
import Girth.ContactZeroJoinTrees

/-! From copy-only qualitative completion to mixed completion.
Each requested edge is attached at an owner copy. The quantitative
theorem then chooses a minimum completion; no estimate is needed
on the number of nodes in the first completed tree. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I N : Type v}

namespace ContactJoinTree

/-- Attaching a contained piece as a leaf does not require any
intersection analysis beyond containment in the parent. -/
theorem insertContained [DecidableEq N] {F : N → Set V}
    {s : Finset N} (T : ContactJoinTree (fun i : {i // i ∈ s} => F i.val))
    (a b : N) (ha : a ∉ s) (hb : b ∈ s) (hsub : F a ⊆ F b) :
    Nonempty (ContactJoinTree (fun i : {i // i ∈ insert a s} => F i.val)) := by
  classical
  let K := {i : N // i ∈ s}
  let U := ContactJoinTree.of_subsingleton (fun _ : PUnit.{v+1} => F a)
  let T' := T.sumBridge U ⟨b,hb⟩ PUnit.unit
    (fun _ _ _ _ hy => ⟨hsub hy,hy⟩)
  let f : K ⊕ PUnit.{v+1} → {i : N // i ∈ insert a s}
    | .inl x => ⟨x.val,Finset.mem_insert_of_mem x.property⟩
    | .inr _ => ⟨a,Finset.mem_insert_self _ _⟩
  have hi : Function.Injective f := by
    intro x y he
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext (congrArg Subtype.val he))
      | inr y =>
        have hx : x.val = a := congrArg Subtype.val he
        exact (ha (hx ▸ x.property)).elim
    | inr x =>
      cases y with
      | inl y =>
        have hy : a = y.val := congrArg Subtype.val he
        exact (ha (hy.symm ▸ y.property)).elim
      | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)
  have hs : Function.Surjective f := by
    intro x
    rcases Finset.mem_insert.mp x.property with hx | hx
    · exact ⟨Sum.inr PUnit.unit,Subtype.ext hx.symm⟩
    · exact ⟨Sum.inl ⟨x.val,hx⟩,rfl⟩
  let r := Equiv.ofBijective f ⟨hi,hs⟩
  have hf : ∀ x : K ⊕ PUnit.{v+1},
      contactSumSets (fun i : K => F i.val) (fun _ : PUnit.{v+1} => F a) x =
        F (r x).val := by
    intro x
    cases x <;> rfl
  have hEq : (fun x : {i // i ∈ insert a s} =>
      contactSumSets (fun i : K => F i.val) (fun _ : PUnit.{v+1} => F a) (r.symm x)) =
      (fun x : {i // i ∈ insert a s} => F x.val) := by
    funext x
    rw [hf,r.apply_symm_apply]
  exact ⟨hEq ▸ T'.reindex r.symm⟩

end ContactJoinTree

namespace OrderOneData
variable (D : OrderOneData V E I E)

/-- A qualitative completion for a family of at most m designated
copies supplies some completion for mixed copy/edge selections
of the same size. Added nodes are still designated copies. -/
theorem mixedCompletion_exists
    (m : ℕ)
    (hCover : ∀ e, ∃ i, e ∈ D.copyEdges i)
    (hSub : ∀ i e, e ∈ D.copyEdges i → D.edgeCarrier e ⊆ D.copyCarrier i)
    (hComp : ∀ s : Finset I, s.Nonempty → s.card ≤ m →
      ∃ t : Finset I, s ⊆ t ∧
        Nonempty (ContactJoinTree (fun i : {i // i ∈ t} => D.copyCarrier i.val)))
    (s : Finset (I ⊕ E)) (hs : s.Nonempty) (hm : s.card ≤ m) :
    ∃ t : Finset (I ⊕ E), s ⊆ t ∧
      (∀ a ∈ t, a ∉ s → ∃ i, a = Sum.inl i) ∧
      Nonempty (ContactJoinTree (fun a : {a // a ∈ t} => D.carrier a.val)) := by
  classical
  let owner : I ⊕ E → I
    | .inl i => i
    | .inr e => Classical.choose (hCover e)
  let s₀ := s.image owner
  have hs₀ : s₀.Nonempty := by
    obtain ⟨a,ha⟩ := hs
    exact ⟨owner a,Finset.mem_image.mpr ⟨a,ha,rfl⟩⟩
  obtain ⟨t₀,hst,⟨T⟩⟩ := hComp s₀ hs₀ (Finset.card_image_le.trans hm)
  let t₁ : Finset (I ⊕ E) := t₀.image Sum.inl
  let r : {i : I // i ∈ t₀} → {a : I ⊕ E // a ∈ t₁} :=
    fun i => ⟨Sum.inl i.val,Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩
  have hri : Function.Injective r := by
    intro i j h
    exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
  have hrs : Function.Surjective r := by
    intro a
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp a.property
    exact ⟨⟨i,hi⟩,Subtype.ext he⟩
  let er := Equiv.ofBijective r ⟨hri,hrs⟩
  have hT₁ : Nonempty (ContactJoinTree (fun a : {a // a ∈ t₁} => D.carrier a.val)) := by
    have hEq : (fun a : {a // a ∈ t₁} => D.copyCarrier (er.symm a).val) =
        (fun a : {a // a ∈ t₁} => D.carrier a.val) := by
      funext a
      obtain ⟨i,rfl⟩ := er.surjective a
      rw [er.symm_apply_apply]
      rfl
    exact ⟨hEq ▸ T.reindex er.symm⟩
  have aux : ∀ u : Finset (I ⊕ E), u ⊆ s →
      Nonempty (ContactJoinTree (fun a : {a // a ∈ t₁ ∪ u} => D.carrier a.val)) := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
      intro _
      simpa only [Finset.union_empty] using hT₁
    | @insert a u hau ih =>
      intro hus
      have hu : u ⊆ s := fun x hx => hus (Finset.mem_insert_of_mem hx)
      have has : a ∈ s := hus (Finset.mem_insert_self _ _)
      obtain ⟨J⟩ := ih hu
      have heq : t₁ ∪ insert a u = insert a (t₁ ∪ u) := by
        ext x
        simp only [Finset.mem_union,Finset.mem_insert]
        tauto
      rw [heq]
      by_cases ha : a ∈ t₁ ∪ u
      · rw [Finset.insert_eq_of_mem ha]
        exact ⟨J⟩
      · let b : I ⊕ E := Sum.inl (owner a)
        have hb : b ∈ t₁ ∪ u :=
          Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨owner a,hst (Finset.mem_image.mpr ⟨a,has,rfl⟩),rfl⟩)
        have hsub : D.carrier a ⊆ D.carrier b := by
          cases a with
          | inl i => exact Set.Subset.rfl
          | inr e => exact hSub _ e (Classical.choose_spec (hCover e))
        exact J.insertContained a b ha hb hsub
  refine ⟨t₁ ∪ s,Finset.subset_union_right,?_,aux s Finset.Subset.rfl⟩
  intro a ha hn
  have h : a ∈ t₁ := (Finset.mem_union.mp ha).resolve_right hn
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
  exact ⟨i,he.symm⟩

/-- Sharp completion bound in the actual mixed family. The only
qualitative premise is completion of small copy-only selections. -/
theorem mixedCompletion_cost [Fintype V]
    (g m : ℕ) (hg : 2 ≤ g)
    (hlin : ∀ e f, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (hpair : D.ZeroPairwise)
    (hCover : ∀ e, ∃ i, e ∈ D.copyEdges i)
    (hSub : ∀ i e, e ∈ D.copyEdges i → D.edgeCarrier e ⊆ D.copyCarrier i)
    (hG : ∀ i, LabelledGirthGT (fun e : D.copyEdges i => D.edgeCarrier e.val) g)
    (hComp : ∀ s : Finset I, s.Nonempty → s.card ≤ m →
      ∃ t : Finset I, s ⊆ t ∧
        Nonempty (ContactJoinTree (fun i : {i // i ∈ t} => D.copyCarrier i.val)))
    (s : Finset (I ⊕ E)) (hs : 2 ≤ s.card) (hm : s.card ≤ m) :
    ∃ t : Finset (I ⊕ E), s ⊆ t ∧
      (∀ a ∈ t, a ∉ s → ∃ i, a = Sum.inl i) ∧
      Nonempty (ContactJoinTree (fun a : {a // a ∈ t} => D.carrier a.val)) ∧
      (g-1)*(t \ s).card ≤ s.card-2 := by
  classical
  apply contact_minimumCompletion_cost D.carrier D.edgeCarrier D.edges
    (fun a => ∃ i, a = Sum.inl i) g hg hlin ?_ ?_ s hs
  · intro a ha
    obtain ⟨i,rfl⟩ := ha
    exact hG i
  · intro a b hne _
    rcases hpair a b hne with h | ⟨e,he,_,h⟩
    · exact Or.inl h
    · exact Or.inr ⟨e,he,h⟩
  · exact D.mixedCompletion_exists m hCover hSub hComp s
      (Finset.card_pos.mp (by omega)) hm

end OrderOneData
end StructuralRamsey.Girth

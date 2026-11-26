import Girth.ContactCycleCompression
import Girth.ContactJoinTreeGlue
import Girth.ContactZeroJoinTrees
import Girth.ContactTrainData

/-! A small family with a join tree cannot support a Berge cycle
whose connectors lie in a set meeting every pair intersection
in at most one vertex. This is exactly the leaf argument for
the new children of a first wagon in the one-step refinement. -/

namespace StructuralRamsey.Girth
universe v
variable {V I J P : Type v}

theorem contact_joinTree_no_cycle_on_set
    (F : I → Set V) (C : Set V) {g : ℕ}
    (hforest : ∀ s : Finset I, s.Nonempty → s.card ≤ g →
      Nonempty (ContactJoinTree (fun i : {i // i ∈ s} => F i.val)))
    (hinter : ∀ a b : I, a ≠ b → (F a ∩ F b ∩ C).Subsingleton) :
    LabelledGirthGT (fun i => F i ∩ C) g := by
  classical
  rintro ⟨B,hB⟩
  let s := Finset.univ.image B.label
  let i₀ : Fin B.length := ⟨0,by have := B.hlength; omega⟩
  have hs : s.Nonempty := ⟨B.label i₀,Finset.mem_image.mpr ⟨i₀,Finset.mem_univ _,rfl⟩⟩
  have hc : s.card ≤ g := by
    calc
      s.card ≤ (Finset.univ : Finset (Fin B.length)).card := Finset.card_image_le
      _ = B.length := by simp
      _ ≤ g := hB
  obtain ⟨T⟩ := hforest s hs hc
  let idx : Fin B.length → {i // i ∈ s} := fun k =>
    ⟨B.label k,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩
  have hinj : Function.Injective idx := fun i j h => B.label_injective (congrArg Subtype.val h)
  have hsurj : Function.Surjective idx := by
    intro i
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp i.property
    exact ⟨k,Subtype.ext hk⟩
  let J := {i // i ∈ s}
  letI : Nontrivial J := ⟨⟨idx i₀,idx (cyclicSucc i₀),
    fun he => contactSucc_ne B.hlength i₀ (hinj he).symm⟩⟩
  obtain ⟨leaf,parent,hadj,huniq,_⟩ := T.exists_leaf_attachment
  obtain ⟨k,hk⟩ := hsurj leaf
  obtain ⟨prev,hprev⟩ := contactSucc_surjective k
  have hprevne : prev ≠ k := by
    intro he
    exact contactSucc_ne B.hlength k (he ▸ hprev)
  have hxleaf : B.vertex k ∈ F leaf.val := by
    rw [← hk]
    exact (B.left_mem k).1
  have hyleaf : B.vertex prev ∈ F leaf.val := by
    rw [← hk]
    have h := (B.right_mem prev).1
    rw [hprev] at h
    exact h
  have hxparent := T.mem_parent_of_mem_leaf_and_other hadj huniq
    (show idx (cyclicSucc k) ≠ leaf from fun he =>
      contactSucc_ne B.hlength k (hinj (he.trans hk.symm)))
    hxleaf (show B.vertex k ∈ F (idx (cyclicSucc k)).val from (B.right_mem k).1)
  have hyparent := T.mem_parent_of_mem_leaf_and_other hadj huniq
    (show idx prev ≠ leaf from fun he => hprevne (hinj (he.trans hk.symm)))
    hyleaf (show B.vertex prev ∈ F (idx prev).val from (B.left_mem prev).1)
  have he := hinter leaf.val parent.val (fun h => hadj.ne (Subtype.ext h))
    ⟨⟨hxleaf,hxparent⟩,(B.left_mem k).2⟩
    ⟨⟨hyleaf,hyparent⟩,(B.left_mem prev).2⟩
  exact hprevne (B.vertex_injective he.symm)

/-- A labelled family refined into smaller carriers has girth
through g if its coarser family does, and no short cycle of the
refined family is contained in a single parent. -/
theorem contact_girth_of_parent (F : I → Set V) (K : P → Set V)
    (parent : I → P) {g : ℕ}
    (hsub : ∀ i, F i ⊆ K (parent i))
    (hg : LabelledGirthGT K g)
    (hlocal : ∀ C : LabelledBergeCycle F, C.length ≤ g →
      (∀ i j, parent (C.label i) = parent (C.label j)) → False) :
    LabelledGirthGT F g := by
  classical
  rintro ⟨C,hC⟩
  apply hlocal C hC
  let own : Fin C.length → P := fun i => parent (C.label i)
  have hconst : ∃ a, ∀ i, own i = a := by
    by_contra hn
    obtain ⟨B,hB⟩ := C.contact_compress_owners own K (fun i => hsub (C.label i)) hn
    have hc : contactOwnerChanges own ≤ C.length := by
      rw [← contactOwnerCutPositions_card own]
      simpa using Finset.card_le_card (Finset.subset_univ (contactOwnerCutPositions own))
    exact hg ⟨B,hB.trans (hc.trans hC)⟩
  obtain ⟨p,hp⟩ := hconst
  intro i j
  exact (hp i).trans (hp j).symm

/-- New child wagons within one parent carry distinct standard
labels. Their switch vertices lie in the common single part and
in the corresponding core copies. A short cycle would therefore
be a forbidden leaf-cycle in the selected core-copy family. -/
theorem contact_split_child_girth
    (F : J → Set V) (K : P → Set V) (parent : J → P)
    (standard : J → I) (coreCopy : I → Set V) (allowed : Set V)
    {g : ℕ} (hg : LabelledGirthGT K g)
    (hsub : ∀ j, F j ⊆ K (parent j))
    (hstandard : ∀ a b, parent a = parent b →
      standard a = standard b → a = b)
    (htrace : ∀ a b, a ≠ b → parent a = parent b →
      F a ∩ F b ⊆ coreCopy (standard a) ∩ coreCopy (standard b) ∩ allowed)
    (hforest : ∀ s : Finset I, s.Nonempty → s.card ≤ g →
      Nonempty (ContactJoinTree (fun i : {i // i ∈ s} => coreCopy i.val)))
    (hinter : ∀ a b, a ≠ b →
      (coreCopy a ∩ coreCopy b ∩ allowed).Subsingleton) :
    LabelledGirthGT F g := by
  apply contact_girth_of_parent F K parent hsub hg
  intro C hC hparent
  have hne : ∀ i, C.label i ≠ C.label (cyclicSucc i) :=
    fun i h => contactSucc_ne C.hlength i (C.label_injective h).symm
  let B : LabelledBergeCycle (fun i => coreCopy i ∩ allowed) := {
    length := C.length
    hlength := C.hlength
    label := standard ∘ C.label
    vertex := C.vertex
    label_injective := fun i j he =>
      C.label_injective (hstandard _ _ (hparent i j) he)
    vertex_injective := C.vertex_injective
    left_mem := fun i => by
      have h := htrace _ _ (hne i) (hparent i _) ⟨C.left_mem i,C.right_mem i⟩
      exact ⟨h.1.1,h.2⟩
    right_mem := fun i => by
      have h := htrace _ _ (hne i) (hparent i _) ⟨C.left_mem i,C.right_mem i⟩
      exact ⟨h.1.2,h.2⟩
  }
  exact contact_joinTree_no_cycle_on_set coreCopy allowed hforest hinter ⟨B,hC⟩

end StructuralRamsey.Girth

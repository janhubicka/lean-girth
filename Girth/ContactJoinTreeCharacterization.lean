import Girth.ContactJoinTreeConverse
import Girth.ContactJoinTreeCycles

/-! Complete the finite join-tree characterization. The forward
direction is a direct leaf argument and the converse is the
contained-member/private-vertex elimination proved in the previous
module. No chordality or clique-tree theorem is an axiom. -/

namespace StructuralRamsey.Girth
universe v
variable {W I : Type v}

namespace ContactJoinTree

/-- A finite family with a join tree is conformal. If a clique
contains a point exclusive to the leaf, it is covered by the leaf.
Otherwise every point of that clique in the leaf belongs also to
the parent; all its witnesses survive leaf deletion. -/
theorem conformal [Fintype I] {F : I → Set W} (T : ContactJoinTree F) :
    ContactConformal F := by
  classical
  intro s hs hv hp
  have aux : ∀ n : ℕ, ∀ (J : Type v) [Fintype J], Fintype.card J = n →
      ∀ K : J → Set W, ContactJoinTree K →
      (∀ x ∈ s, ∃ i, x ∈ K i) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∃ i, x ∈ K i ∧ y ∈ K i) →
      ∃ i, (↑s : Set W) ⊆ K i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J inst hn K T hv hp
      by_cases hsub : Subsingleton J
      · letI : Subsingleton J := hsub
        obtain ⟨x,hx⟩ := hs
        obtain ⟨i,hi⟩ := hv x hx
        refine ⟨i,?_⟩
        intro y hy
        obtain ⟨j,hj⟩ := hv y hy
        simpa only [Subsingleton.elim j i] using hj
      · letI : Nontrivial J := not_subsingleton_iff_nontrivial.mp hsub
        obtain ⟨leaf,parent,hadj,huniq,_⟩ := T.exists_leaf_attachment
        by_cases hpriv : ∃ x ∈ s, x ∈ K leaf ∧
            ∀ j : J, x ∈ K j → j = leaf
        · obtain ⟨x,hx,hxl,honly⟩ := hpriv
          refine ⟨leaf,?_⟩
          intro y hy
          by_cases hxy : x = y
          · simpa only [← hxy] using hxl
          · obtain ⟨j,hxj,hyj⟩ := hp x hx y hy hxy
            simpa only [honly j hxj] using hyj
        · have hother : ∀ x ∈ s, ∃ j : J, j ≠ leaf ∧ x ∈ K j := by
            intro x hx
            by_contra hnot
            have hone : ∀ j : J, x ∈ K j → j = leaf := by
              intro j hj
              by_contra hne
              exact hnot ⟨j,hne,hj⟩
            obtain ⟨j,hj⟩ := hv x hx
            exact hpriv ⟨x,hx,by simpa only [hone j hj] using hj,hone⟩
          let J' := {j : J // j ∈ ({leaf} : Set J)ᶜ}
          letI : Fintype J' := Fintype.ofFinite J'
          have hlt : Fintype.card J' < n := by
            rw [← hn]
            apply Fintype.card_lt_of_injective_not_surjective (fun i : J' => i.val)
              Subtype.val_injective
            intro hsur
            obtain ⟨x,hx⟩ := hsur leaf
            have hne : x.val ≠ leaf := by
              simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using x.property
            exact hne hx
          have hvertex : ∀ x ∈ s, ∃ i : J', x ∈ contactEraseSet K leaf i := by
            intro x hx
            obtain ⟨j,hne,hj⟩ := hother x hx
            exact ⟨⟨j,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hne⟩,hj⟩
          have hpair : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∃ i : J',
              x ∈ contactEraseSet K leaf i ∧ y ∈ contactEraseSet K leaf i := by
            intro x hx y hy hxy
            obtain ⟨j,hxj,hyj⟩ := hp x hx y hy hxy
            by_cases hne : j = leaf
            · subst j
              obtain ⟨k,hk,hxk⟩ := hother x hx
              obtain ⟨l,hl,hyl⟩ := hother y hy
              exact ⟨⟨parent,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff]
                using hadj.ne.symm⟩,
                T.mem_parent_of_mem_leaf_and_other hadj huniq hk hxj hxk,
                T.mem_parent_of_mem_leaf_and_other hadj huniq hl hyj hyl⟩
            · exact ⟨⟨j,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hne⟩,
                hxj,hyj⟩
          obtain ⟨j,hj⟩ := ih _ hlt J' rfl (contactEraseSet K leaf)
            (T.eraseLeaf hadj huniq) hvertex hpair
          exact ⟨j.val,hj⟩
  exact aux _ I rfl F T hv hp

/-- The two-section of a finite join-tree family is chordal. The
already proved support-clique polygon theorem supplies the chord. -/
theorem chordal [Fintype I] {F : I → Set W} (T : ContactJoinTree F) :
    ContactChordal (contactFamilyGraph F) := by
  classical
  intro n z hn hInj hside
  let supp : W ⊕ PUnit.{v+1} → Set W
    | .inl x => {x}
    | .inr _ => ∅
  let K : I → Set (W ⊕ PUnit.{v+1}) := fun i => {z | supp z ⊆ F i}
  let C : ContactPolygon W PUnit.{v+1} := {
    length := n
    hlength := by omega
    vertex := fun i => Sum.inl (z i)
    vertex_injective := fun _ _ h => hInj (Sum.inl.inj h)
  }
  have hc : C.IsCycle K := by
    intro i
    obtain ⟨hne,j,hx,hy⟩ := hside i
    exact ⟨fun he => hne (Sum.inl.inj he),j,
      fun x hx' => by have he : x = z i := hx'; simpa only [he] using hx,
      fun x hx' => by have he : x = z (cyclicSucc i) := hx'; simpa only [he] using hy⟩
  have hw : C.twiceWeight ≤ 2*n := by
    simp [ContactPolygon.twiceWeight,C,contactWeight,contactKind,
      twiceOccurrenceWeight,Nat.mul_comm]
  obtain ⟨i,j,hnc,hadj⟩ := ((T.g4_of_support supp n) C hc hw).2 hn
  obtain ⟨hne,a,hi,hj⟩ := hadj
  exact ⟨i,j,hnc.1,hnc.2.1,hnc.2.2,
    fun he => hne (congrArg Sum.inl he),a,hi rfl,hj rfl⟩

end ContactJoinTree

/-- Running-intersection trees on actual labels are equivalent to
chordality and conformality of the finite used-vertex two-section. -/
theorem contact_joinTree_iff [Fintype W] [Fintype I] [Nonempty I]
    (F : I → Set W) :
    Nonempty (ContactJoinTree F) ↔
      ContactChordal (contactFamilyGraph F) ∧ ContactConformal F := by
  constructor
  · rintro ⟨T⟩
    exact ⟨T.chordal,T.conformal⟩
  · rintro ⟨hch,hc⟩
    exact contact_joinTree_of_chordal_conformal F hch hc

end StructuralRamsey.Girth

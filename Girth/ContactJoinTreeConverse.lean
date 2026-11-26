import Girth.ContactSimplicial
import Girth.ContactJoinTreeRestore

/-! Constructive chordal/conformal converse for finite set families.
The induction is GYO elimination: either remove a contained member,
or choose a simplicial vertex of the graph on the used vertices.
Conformality puts its closed neighbourhood in one member, making
it private once all contained members are removed. Restoring a
private vertex or a contained member is already implemented by
actual join-tree constructions. -/

namespace StructuralRamsey.Girth
universe v
variable {W I : Type v}

def contactFamilyGraph (F : I → Set W) : SimpleGraph W where
  Adj x y := x ≠ y ∧ ∃ i, x ∈ F i ∧ y ∈ F i
  symm := {symm := by
    intro x y h
    obtain ⟨hne,i,hx,hy⟩ := h
    exact ⟨hne.symm,i,hy,hx⟩}
  loopless := {irrefl := fun _ h => h.1 rfl}

def ContactConformal (F : I → Set W) : Prop :=
  ∀ s : Finset W, s.Nonempty →
    (∀ x ∈ s, ∃ i, x ∈ F i) →
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∃ i, x ∈ F i ∧ y ∈ F i) →
    ∃ i, (↑s : Set W) ⊆ F i

noncomputable def contactUsedVertices [Fintype W] (F : I → Set W) : Finset W := by
  classical
  exact Finset.univ.filter (fun x => ∃ i, x ∈ F i)

theorem mem_contactUsedVertices [Fintype W] (F : I → Set W) (x : W) :
    x ∈ contactUsedVertices F ↔ ∃ i, x ∈ F i := by
  classical
  simp [contactUsedVertices]

/-- When a member is contained in another one, deleting it changes
neither the graph nor the used vertices. -/
theorem contact_eraseContained_graph {F : I → Set W} {a b : I}
    (hne : b ≠ a) (hsub : F a ⊆ F b) :
    contactFamilyGraph (contactEraseSet F a) = contactFamilyGraph F := by
  classical
  ext x y
  constructor
  · rintro ⟨hxy,i,hx,hy⟩
    exact ⟨hxy,i.val,hx,hy⟩
  · rintro ⟨hxy,i,hx,hy⟩
    by_cases hi : i = a
    · subst i
      exact ⟨hxy,⟨b,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hne⟩,
        hsub hx,hsub hy⟩
    · exact ⟨hxy,⟨i,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hi⟩,
        hx,hy⟩

theorem contact_eraseContained_used [Fintype W] {F : I → Set W} {a b : I}
    (hne : b ≠ a) (hsub : F a ⊆ F b) :
    contactUsedVertices (contactEraseSet F a) = contactUsedVertices F := by
  classical
  ext x
  rw [mem_contactUsedVertices,mem_contactUsedVertices]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i.val,hi⟩
  · rintro ⟨i,hi⟩
    by_cases he : i = a
    · subst i
      exact ⟨⟨b,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hne⟩,hsub hi⟩
    · exact ⟨⟨i,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using he⟩,hi⟩

theorem contact_eraseContained_conformal {F : I → Set W} {a b : I}
    (hne : b ≠ a) (hsub : F a ⊆ F b) (hc : ContactConformal F) :
    ContactConformal (contactEraseSet F a) := by
  classical
  intro s hs hv hp
  obtain ⟨i,hi⟩ := hc s hs
    (fun x hx => by obtain ⟨j,hj⟩ := hv x hx; exact ⟨j.val,hj⟩)
    (fun x hx y hy hxy => by
      obtain ⟨j,hj,hj'⟩ := hp x hx y hy hxy
      exact ⟨j.val,hj,hj'⟩)
  by_cases he : i = a
  · subst i
    exact ⟨⟨b,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hne⟩,
      hi.trans hsub⟩
  · exact ⟨⟨i,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using he⟩,hi⟩

/-- Removing one vertex induces the graph on the remaining used
vertices, together with the now isolated deleted vertex. -/
theorem contact_removeVertex_chordal {F : I → Set W} (x : W)
    (hch : ContactChordal (contactFamilyGraph F)) :
    ContactChordal (contactFamilyGraph (fun i => F i \ {x})) := by
  intro n z hn hInj hside
  have hnot : ∀ i, z i ≠ x := by
    intro i
    obtain ⟨_,a,ha,_⟩ := hside i
    exact ha.2
  have hside' : ∀ i, (contactFamilyGraph F).Adj (z i) (z (cyclicSucc i)) := by
    intro i
    obtain ⟨hne,a,ha,hb⟩ := hside i
    exact ⟨hne,a,ha.1,hb.1⟩
  obtain ⟨i,j,hij,h1,h2,h3⟩ := hch n z hn hInj hside'
  obtain ⟨hne,a,ha,hb⟩ := h3
  exact ⟨i,j,hij,h1,h2,hne,a,⟨ha,hnot i⟩,⟨hb,hnot j⟩⟩

theorem contact_removeVertex_conformal {F : I → Set W} (x : W)
    (hc : ContactConformal F) : ContactConformal (fun i => F i \ {x}) := by
  intro s hs hv hp
  obtain ⟨a,ha⟩ := hc s hs
    (fun u hu => by obtain ⟨j,hj⟩ := hv u hu; exact ⟨j,hj.1⟩)
    (fun u hu w hw hne => by
      obtain ⟨j,hj,hj'⟩ := hp u hu w hw hne
      exact ⟨j,hj.1,hj'.1⟩)
  refine ⟨a,?_⟩
  intro u hu
  obtain ⟨j,hj⟩ := hv u hu
  exact ⟨ha hu,hj.2⟩

open Classical in
theorem contact_removeVertex_used [Fintype W] (F : I → Set W) (x : W) :
    contactUsedVertices (fun i => F i \ {x}) = (contactUsedVertices F).erase x := by
  classical
  ext y
  rw [mem_contactUsedVertices,Finset.mem_erase,mem_contactUsedVertices]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨hi.2,i,hi.1⟩
  · rintro ⟨hne,i,hi⟩
    exact ⟨i,hi,hne⟩

/-- In a conformal family with no distinct comparable members, a
simplicial used vertex belongs to exactly one member. -/
theorem contact_private_of_simplicial [Fintype W] {F : I → Set W}
    (hc : ContactConformal F)
    (hnc : ∀ i j : I, F i ⊆ F j → i = j)
    (x : W) (hx : x ∈ contactUsedVertices F)
    (hs : ContactSimplicial (contactFamilyGraph F) x) :
    {i : I | x ∈ F i}.Subsingleton := by
  classical
  let G := contactFamilyGraph F
  let s := (contactUsedVertices F).filter (fun y => y = x ∨ G.Adj x y)
  have hxs : x ∈ s := Finset.mem_filter.mpr ⟨hx,Or.inl rfl⟩
  have hmem : ∀ y ∈ s, ∃ i, y ∈ F i :=
    fun y hy => (mem_contactUsedVertices F y).mp (Finset.mem_filter.mp hy).1
  have hclique : ∀ y ∈ s, ∀ z ∈ s, y ≠ z →
      ∃ i, y ∈ F i ∧ z ∈ F i := by
    intro y hy z hz hne
    have hadj : G.Adj y z := by
      rcases (Finset.mem_filter.mp hy).2 with he | he
      · subst y
        rcases (Finset.mem_filter.mp hz).2 with he' | he'
        · exact (hne he'.symm).elim
        · exact he'
      · rcases (Finset.mem_filter.mp hz).2 with he' | he'
        · subst z
          exact he.symm
        · exact hs y z he he' hne
    exact hadj.2
  obtain ⟨a,ha⟩ := hc s ⟨x,hxs⟩ hmem hclique
  have huniq : ∀ i : I, x ∈ F i → i = a := by
    intro i hi
    apply hnc
    intro y hy
    apply ha
    apply Finset.mem_filter.mpr
    refine ⟨(mem_contactUsedVertices F y).mpr ⟨i,hy⟩,?_⟩
    by_cases he : y = x
    · exact Or.inl he
    · exact Or.inr ⟨he.symm,i,hi,hy⟩
  intro i hi j hj
  exact (huniq i hi).trans (huniq j hj).symm

/-- The graph on the used vertices has a simplicial vertex; as unused
vertices are isolated, it is simplicial in the full family graph. -/
theorem contact_family_simplicial_used [Fintype W] (F : I → Set W)
    (hch : ContactChordal (contactFamilyGraph F))
    (hused : (contactUsedVertices F).Nonempty) :
    ∃ x ∈ contactUsedVertices F, ContactSimplicial (contactFamilyGraph F) x := by
  classical
  let U : Set W := ↑(contactUsedVertices F)
  let L := {x : W // x ∈ U}
  letI : Fintype L := Fintype.ofFinite L
  letI : Nonempty L := by obtain ⟨x,hx⟩ := hused; exact ⟨⟨x,hx⟩⟩
  let G := contactFamilyGraph F
  obtain ⟨x,hx⟩ := contact_exists_simplicial (G.induce U)
    (contactChordal_induce hch U)
  refine ⟨x.val,x.property,?_⟩
  intro y z hy hz hne
  have hy' : y ∈ U := by
    obtain ⟨_,i,_,hi⟩ := hy
    exact (mem_contactUsedVertices F y).mpr ⟨i,hi⟩
  have hz' : z ∈ U := by
    obtain ⟨_,i,_,hi⟩ := hz
    exact (mem_contactUsedVertices F z).mpr ⟨i,hi⟩
  exact hx ⟨y,hy'⟩ ⟨z,hz'⟩ hy hz (fun he => hne (congrArg Subtype.val he))

/-- Finite chordal and conformal set families have a join tree on
their actual labels. The induction measure is the number of members
plus the number of used vertices, so both elimination moves decrease
it. Duplicate and empty members are retained in the final tree. -/
theorem contact_joinTree_of_chordal_conformal [Fintype W] [Fintype I] [Nonempty I]
    (F : I → Set W) (hch : ContactChordal (contactFamilyGraph F))
    (hc : ContactConformal F) : Nonempty (ContactJoinTree F) := by
  classical
  have aux : ∀ n : ℕ, ∀ (J : Type v) [Fintype J] [Nonempty J],
      ∀ K : J → Set W, Fintype.card J + (contactUsedVertices K).card = n →
        ContactChordal (contactFamilyGraph K) → ContactConformal K →
        Nonempty (ContactJoinTree K) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J inst fin K hn hch hc
      by_cases hsub : Subsingleton J
      · letI : Subsingleton J := hsub
        exact ⟨ContactJoinTree.of_subsingleton K⟩
      · letI : Nontrivial J := not_subsingleton_iff_nontrivial.mp hsub
        by_cases hcont : ∃ a b : J, a ≠ b ∧ K a ⊆ K b
        · obtain ⟨a,b,hab,hK⟩ := hcont
          let J' := {i : J // i ∈ ({a} : Set J)ᶜ}
          letI : Fintype J' := Fintype.ofFinite J'
          letI : Nonempty J' := ⟨⟨b,by
            simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hab.symm⟩⟩
          let K' := contactEraseSet K a
          have hlt : Fintype.card J' < Fintype.card J := by
            apply Fintype.card_lt_of_injective_not_surjective (fun i : J' => i.val)
              Subtype.val_injective
            intro hs
            obtain ⟨x,hx⟩ := hs a
            have hne : x.val ≠ a := by
              simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using x.property
            exact hne hx
          have hUsed : contactUsedVertices K' = contactUsedVertices K :=
            contact_eraseContained_used hab.symm hK
          have hrank : Fintype.card J' + (contactUsedVertices K').card < n := by
            rw [hUsed]
            omega
          have hch' : ContactChordal (contactFamilyGraph K') := by
            change ContactChordal (contactFamilyGraph (contactEraseSet K a))
            rw [contact_eraseContained_graph hab.symm hK]
            exact hch
          obtain ⟨T⟩ := ih _ hrank J' K' rfl hch'
            (contact_eraseContained_conformal hab.symm hK hc)
          exact ⟨ContactJoinTree.restoreContained a b hab.symm T hK⟩
        · have hnc : ∀ a b : J, K a ⊆ K b → a = b := by
            intro a b h
            by_contra he
            exact hcont ⟨a,b,he,h⟩
          have hused : (contactUsedVertices K).Nonempty := by
            by_contra h
            obtain ⟨a,b,hab⟩ := exists_pair_ne J
            apply hab
            apply hnc
            intro x hx
            exact (h ⟨x,(mem_contactUsedVertices K x).mpr ⟨a,hx⟩⟩).elim
          obtain ⟨x,hx,hs⟩ := contact_family_simplicial_used K hch hused
          have hpriv := contact_private_of_simplicial hc hnc x hx hs
          let K' : J → Set W := fun i => K i \ {x}
          have hrank : Fintype.card J + (contactUsedVertices K').card < n := by
            change Fintype.card J + (contactUsedVertices (fun i => K i \ {x})).card < n
            rw [contact_removeVertex_used]
            have hlt := Finset.card_erase_lt_of_mem hx
            omega
          obtain ⟨T⟩ := ih _ hrank J K' rfl (contact_removeVertex_chordal x hch)
            (contact_removeVertex_conformal x hc)
          exact ⟨ContactJoinTree.restorePrivate x T hpriv⟩
  exact aux _ I F rfl hch hc

end StructuralRamsey.Girth

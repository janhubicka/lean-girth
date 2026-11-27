import Girth.ContactJoinTreeRestore
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Parent-first and admissible enumerations of finite join trees.

An enumeration is represented by an injective natural-number rank; gaps in
the ranks are immaterial. The preceding-union equality is an actual equality
of sets, rather than a condition on pairwise intersections alone. -/

namespace StructuralRamsey.Girth
universe v
variable {W I : Type v}

namespace ContactJoinTree

/-- A new node attached to a connected initial subtree meets its union
exactly in its parent separator. -/
theorem inter_preconnected_eq_parent {F : I → Set W}
    (J : ContactJoinTree F) (S : Set I) (hS : (J.tree.induce S).Preconnected)
    {i p : I} (hi : i ∉ S) (hp : p ∈ S) (hadj : J.tree.Adj i p) :
    F i ∩ (⋃ j : S, F j.val) = F i ∩ F p := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨hxi,hxS⟩
    obtain ⟨j,hxj⟩ := Set.mem_iUnion.mp hxS
    obtain ⟨q,hq⟩ := (hS ⟨p,hp⟩ j).exists_isPath
    let q' := q.map (SimpleGraph.Embedding.induce S).toHom
    have hq' : q'.IsPath := hq.map
      (SimpleGraph.Embedding.induce (G := J.tree) S).injective
    have hiq : i ∉ q'.support := by
      intro hm
      rw [SimpleGraph.Walk.support_map] at hm
      obtain ⟨a,_,ha⟩ := List.mem_map.mp hm
      exact hi (ha ▸ a.property)
    let t := SimpleGraph.Walk.cons hadj q'
    have ht : t.IsPath := (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hq',hiq⟩
    obtain ⟨r,hr⟩ := (J.running x ⟨i,hxi⟩ ⟨j.val,hxj⟩).exists_isPath
    let r' := r.map (SimpleGraph.Embedding.induce {k : I | x ∈ F k}).toHom
    have hr' : r'.IsPath := hr.map
      (SimpleGraph.Embedding.induce (G := J.tree) {k : I | x ∈ F k}).injective
    have he : t = r' := congrArg Subtype.val
      ((J.isTree.isAcyclic.subsingleton_path i j.val).elim ⟨t,ht⟩ ⟨r',hr'⟩)
    have hpm : p ∈ r'.support := by
      rw [← he]
      exact List.mem_cons_of_mem i q'.start_mem_support
    rw [SimpleGraph.Walk.support_map] at hpm
    obtain ⟨a,_,ha⟩ := List.mem_map.mp hpm
    exact ⟨hxi,ha ▸ a.property⟩
  · rintro x ⟨hxi,hxp⟩
    exact ⟨hxi,Set.mem_iUnion.mpr ⟨⟨p,hp⟩,hxp⟩⟩

/-- Every initial set in a parent-first ranking is connected. -/
theorem parentFirst_preconnected {F : I → Set W}
    (J : ContactJoinTree F) (root : I) (parent : I → I) (rank : I → ℕ)
    (hparent : ∀ i, i ≠ root →
      J.tree.Adj i (parent i) ∧ rank (parent i) < rank i)
    (k : ℕ) : (J.tree.induce {i | rank i < k}).Preconnected := by
  classical
  have aux : ∀ n : ℕ, ∀ i : I, rank i = n → ∀ hik : rank i < k,
      ∃ hr : rank root < k,
        (J.tree.induce {i | rank i < k}).Reachable ⟨i,hik⟩ ⟨root,hr⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hin hik
      by_cases he : i = root
      · subst i
        exact ⟨hik,SimpleGraph.Reachable.refl _⟩
      · obtain ⟨ha,hl⟩ := hparent i he
        obtain ⟨hr,ht⟩ := ih (rank (parent i)) (by omega) (parent i) rfl (by omega)
        have ha' : (J.tree.induce {i | rank i < k}).Adj
            ⟨i,hik⟩ ⟨parent i,lt_trans hl hik⟩ := ha
        exact ⟨hr,ha'.reachable.trans ht⟩
  intro a b
  obtain ⟨ha,hpa⟩ := aux (rank a.val) a.val rfl a.property
  obtain ⟨hb,hpb⟩ := aux (rank b.val) b.val rfl b.property
  exact hpa.trans hpb.symm

/-- The separator equality for any parent-first listing of a rooted join tree. -/
theorem parentFirst_inter_eq {F : I → Set W}
    (J : ContactJoinTree F) (root : I) (parent : I → I) (rank : I → ℕ)
    (hparent : ∀ i, i ≠ root →
      J.tree.Adj i (parent i) ∧ rank (parent i) < rank i)
    (i : I) (hi : i ≠ root) :
    F i ∩ (⋃ j : {j // rank j < rank i}, F j.val) = F i ∩ F (parent i) :=
  J.inter_preconnected_eq_parent _ (J.parentFirst_preconnected root parent rank hparent _)
    (Nat.lt_irrefl _) (hparent i hi).2 (hparent i hi).1

end ContactJoinTree

/-- An admissible enumeration: every noninitial member meets the preceding
union exactly in its intersection with one earlier member. -/
def ContactAdmissibleRank (F : I → Set W) (rank : I → ℕ) : Prop :=
  Function.Injective rank ∧ ∀ i, (∃ j, rank j < rank i) →
    ∃ p, rank p < rank i ∧
      F i ∩ (⋃ j : {j // rank j < rank i}, F j.val) = F i ∩ F p

/-- The converse direction of the admissible-enumeration remark. -/
theorem contact_joinTree_of_admissibleRank [Fintype I] [Nonempty I]
    (F : I → Set W) (rank : I → ℕ) (h : ContactAdmissibleRank F rank) :
    Nonempty (ContactJoinTree F) := by
  classical
  have aux : ∀ n : ℕ, ∀ (K : Type v) [Fintype K] [Nonempty K],
      Fintype.card K = n → ∀ (G : K → Set W) (r : K → ℕ),
      ContactAdmissibleRank G r → Nonempty (ContactJoinTree G) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K inst fin hn G r hr
      by_cases hsub : Subsingleton K
      · let : Subsingleton K := hsub
        exact ⟨ContactJoinTree.of_subsingleton G⟩
      · let : Nontrivial K := not_subsingleton_iff_nontrivial.mp hsub
        obtain ⟨a,_,ha⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
        have hamax (j : K) : r j ≤ r a := ha j (Finset.mem_univ j)
        have halt (j : K) (hj : j ≠ a) : r j < r a :=
          lt_of_le_of_ne (hamax j) (fun he => hj (hr.1 he))
        obtain ⟨b,hb⟩ := exists_ne a
        obtain ⟨p,hp,htrace⟩ := hr.2 a ⟨b,halt b hb⟩
        let K' := {j : K // j ∈ ({a} : Set K)ᶜ}
        let : Fintype K' := Fintype.ofFinite K'
        let : Nonempty K' := ⟨⟨b,by simpa using hb⟩⟩
        have hlt : Fintype.card K' < n := by
          rw [← hn]
          apply Fintype.card_lt_of_injective_not_surjective
            (fun j : K' => j.val) Subtype.val_injective
          intro hs
          obtain ⟨j,hj⟩ := hs a
          exact j.property (Set.mem_singleton_iff.mpr hj)
        have hr' : ContactAdmissibleRank (contactEraseSet G a) (fun j : K' => r j.val) := by
          refine ⟨hr.1.comp Subtype.val_injective,?_⟩
          intro i hi
          obtain ⟨j,hj⟩ := hi
          obtain ⟨q,hq,hqtrace⟩ := hr.2 i.val ⟨j.val,hj⟩
          have hqne : q ≠ a := by
            intro he
            rw [he] at hq
            have := hamax i.val
            omega
          refine ⟨⟨q,by simpa using hqne⟩,hq,?_⟩
          change G i.val ∩ (⋃ j : {j : K' // r j.val < r i.val}, G j.val.val) = G i.val ∩ G q
          rw [← hqtrace]
          congr 1
          ext x
          constructor
          · intro hx
            obtain ⟨j,hxj⟩ := Set.mem_iUnion.mp hx
            exact Set.mem_iUnion.mpr ⟨⟨j.val.val,j.property⟩,hxj⟩
          · intro hx
            obtain ⟨j,hxj⟩ := Set.mem_iUnion.mp hx
            have hjne : j.val ≠ a := by
              intro he
              have := hamax i.val
              have hjlt := j.property
              rw [he] at hjlt
              omega
            exact Set.mem_iUnion.mpr ⟨⟨⟨j.val,by simpa using hjne⟩,j.property⟩,hxj⟩
        obtain ⟨T⟩ := ih _ hlt K' rfl (contactEraseSet G a) (fun j => r j.val) hr'
        refine ⟨ContactJoinTree.attachLeaf a p (by intro he; rw [he] at hp; omega) T ?_⟩
        intro x hxa j hja hxj
        have hx : x ∈ G a ∩ (⋃ k : {k // r k < r a}, G k.val) :=
          ⟨hxa,Set.mem_iUnion.mpr ⟨⟨j,halt j hja⟩,hxj⟩⟩
        rw [htrace] at hx
        exact hx.2
  exact aux (Fintype.card I) I rfl F rank h

/-- Empty or singleton preceding intersections and separators contained in
one earlier member give the exact admissible-ranking condition. In particular,
an edge common to the new member and an earlier member is sufficient. -/
theorem contact_admissibleRank_of_attachments (F : I → Set W) (rank : I → ℕ)
    (hinj : Function.Injective rank)
    (hattach : ∀ i, (∃ j, rank j < rank i) →
      (F i ∩ (⋃ j : {j // rank j < rank i}, F j.val)).Subsingleton ∨
      ∃ p, rank p < rank i ∧
        F i ∩ (⋃ j : {j // rank j < rank i}, F j.val) ⊆ F p) :
    ContactAdmissibleRank F rank := by
  classical
  refine ⟨hinj,?_⟩
  intro i hi
  have aux (p : I) (hp : rank p < rank i)
      (hs : F i ∩ (⋃ j : {j // rank j < rank i}, F j.val) ⊆ F p) :
      ∃ p, rank p < rank i ∧
        F i ∩ (⋃ j : {j // rank j < rank i}, F j.val) = F i ∩ F p := by
    refine ⟨p,hp,Set.Subset.antisymm (fun x hx => ⟨hx.1,hs hx⟩) ?_⟩
    rintro x ⟨hxi,hxp⟩
    exact ⟨hxi,Set.mem_iUnion.mpr ⟨⟨p,hp⟩,hxp⟩⟩
  rcases hattach i hi with hs | ⟨p,hp,hsub⟩
  · by_cases hne : (F i ∩ (⋃ j : {j // rank j < rank i}, F j.val)).Nonempty
    · obtain ⟨x,hx⟩ := hne
      obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hx.2
      apply aux p.val p.property
      intro y hy
      have hxy : x = y := hs hx hy
      rw [← hxy]
      exact hp
    · obtain ⟨p,hp⟩ := hi
      exact aux p hp (fun _ hx => (hne ⟨_,hx⟩).elim)
  · exact aux p hp hsub

theorem contact_joinTree_of_admissibleAttachments [Fintype I] [Nonempty I]
    (F : I → Set W) (rank : I → ℕ) (hinj : Function.Injective rank)
    (hattach : ∀ i, (∃ j, rank j < rank i) →
      (F i ∩ (⋃ j : {j // rank j < rank i}, F j.val)).Subsingleton ∨
      ∃ p, rank p < rank i ∧
        F i ∩ (⋃ j : {j // rank j < rank i}, F j.val) ⊆ F p) :
    Nonempty (ContactJoinTree F) :=
  contact_joinTree_of_admissibleRank F rank
    (contact_admissibleRank_of_attachments F rank hinj hattach)

end StructuralRamsey.Girth

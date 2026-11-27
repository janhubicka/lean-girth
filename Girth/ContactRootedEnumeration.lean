import Girth.ContactEnumeration

/-! Every finite join tree has a parent-first admissible enumeration.
Distance from a chosen root, with an injective finite tie-breaker, supplies
an explicit ranking. Any specified leaf can instead be listed last.
-/

namespace StructuralRamsey.Girth
universe v
variable {W I : Type v}

namespace ContactJoinTree
variable {F : I → Set W} (J : ContactJoinTree F)

/-- The unique path from the root to a node. -/
noncomputable def rootPath (root i : I) : J.tree.Walk root i :=
  Classical.choose (J.isTree.existsUnique_path root i)

theorem rootPath_isPath (root i : I) : (J.rootPath root i).IsPath :=
  (Classical.choose_spec (J.isTree.existsUnique_path root i)).1

theorem rootPath_unique (root i : I) (p : J.tree.Walk root i) (hp : p.IsPath) :
    p = J.rootPath root i :=
  (Classical.choose_spec (J.isTree.existsUnique_path root i)).2 p hp

theorem rootPath_length_eq_dist (root i : I) :
    (J.rootPath root i).length = J.tree.dist root i := by
  obtain ⟨p,hp,hlen⟩ := J.isTree.connected.exists_path_of_dist root i
  have hpi := J.rootPath_unique root i p hp
  simpa [hpi] using hlen

/-- The penultimate node on the unique root path. -/
noncomputable def parent (root i : I) : I := (J.rootPath root i).penultimate

theorem parent_adj (root i : I) (hi : i ≠ root) :
    J.tree.Adj (J.parent root i) i :=
  (J.rootPath root i).adj_penultimate (SimpleGraph.Walk.not_nil_of_ne hi.symm)

theorem parent_dist_add_one (root i : I) (hi : i ≠ root) :
    J.tree.dist root (J.parent root i) + 1 = J.tree.dist root i := by
  let p := J.rootPath root i
  have hp : p.IsPath := J.rootPath_isPath root i
  have hnp : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hi.symm
  have huniq : p.dropLast = J.rootPath root (J.parent root i) :=
    J.rootPath_unique root (J.parent root i) p.dropLast hp.dropLast
  calc
    J.tree.dist root (J.parent root i) + 1 =
        (J.rootPath root (J.parent root i)).length + 1 := by
          rw [J.rootPath_length_eq_dist]
    _ = p.dropLast.length + 1 := by
      rw [← huniq]
      rfl
    _ = p.length := p.length_dropLast_add_one hnp
    _ = J.tree.dist root i := J.rootPath_length_eq_dist root i

/-- Parent-first ranking: root distance is the primary key and an
arbitrary finite enumeration breaks ties injectively. -/
noncomputable def parentFirstRank [Fintype I] (root i : I) : ℕ :=
  J.tree.dist root i * Fintype.card I + (Fintype.equivFin I i).val

theorem parentFirstRank_injective [Fintype I] (root : I) :
    Function.Injective (J.parentFirstRank root) := by
  intro i j he
  have hm := congrArg (fun n => n % Fintype.card I) he
  have hi := (Fintype.equivFin I i).isLt
  have hj := (Fintype.equivFin I j).isLt
  simp only [parentFirstRank,Nat.add_mod,Nat.mul_mod,Nat.mod_self,
    Nat.mul_zero,Nat.zero_mod,Nat.zero_add,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] at hm
  exact (Fintype.equivFin I).injective (Fin.ext hm)

theorem parentFirstRank_parent_lt [Fintype I] (root i : I) (hi : i ≠ root) :
    J.parentFirstRank root (J.parent root i) < J.parentFirstRank root i := by
  have hp := (Fintype.equivFin I (J.parent root i)).isLt
  unfold parentFirstRank
  rw [← J.parent_dist_add_one root i hi,Nat.add_mul,Nat.one_mul]
  omega

theorem parentFirstRank_root_lt [Fintype I] (root i : I) (hi : i ≠ root) :
    J.parentFirstRank root root < J.parentFirstRank root i := by
  have hr := (Fintype.equivFin I root).isLt
  unfold parentFirstRank
  rw [SimpleGraph.dist_self,Nat.zero_mul,Nat.zero_add,
    ← J.parent_dist_add_one root i hi,Nat.add_mul,Nat.one_mul]
  omega

/-- The preceding-union separator equality holds for the explicit ranking. -/
theorem parentFirstRank_admissible [Fintype I] (root : I) :
    ContactAdmissibleRank F (J.parentFirstRank root) := by
  refine ⟨J.parentFirstRank_injective root,?_⟩
  intro i ⟨j,hj⟩
  have hi : i ≠ root := by
    intro he
    subst i
    by_cases hjr : j = root
    · subst j
      exact (Nat.lt_irrefl _ hj)
    · exact (Nat.lt_asymm hj (J.parentFirstRank_root_lt root j hjr))
  have hparent (k : I) (hk : k ≠ root) :
      J.tree.Adj k (J.parent root k) ∧
        J.parentFirstRank root (J.parent root k) < J.parentFirstRank root k :=
    ⟨(J.parent_adj root k hk).symm,J.parentFirstRank_parent_lt root k hk⟩
  exact ⟨J.parent root i,(hparent i hi).2,
    J.parentFirst_inter_eq root (J.parent root) (J.parentFirstRank root) hparent i hi⟩

/-- Every specified leaf can be placed last in an admissible listing. -/
theorem exists_admissibleRank_leaf_last [Fintype I] {leaf parent : I}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j, J.tree.Adj leaf j → j = parent) :
    ∃ rank : I → ℕ, ContactAdmissibleRank F rank ∧
      ∀ i, i ≠ leaf → rank i < rank leaf := by
  classical
  let K := {i : I // i ∈ ({leaf} : Set I)ᶜ}
  let : Fintype K := Fintype.ofFinite K
  have hpne : parent ≠ leaf := hadj.ne.symm
  let p : K := ⟨parent,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hpne⟩
  let : Nonempty K := ⟨p⟩
  let T := J.eraseLeaf hadj huniq
  let r := T.parentFirstRank p
  have hr : ContactAdmissibleRank (contactEraseSet F leaf) r :=
    T.parentFirstRank_admissible p
  obtain ⟨a,_,ha⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
  let N := r a + 1
  have hcap (j : K) : r j < N := by
    have := ha j (Finset.mem_univ j)
    omega
  let rank (i : I) : ℕ := if h : i = leaf then N else r ⟨i,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using h⟩
  have hleaf : rank leaf = N := by simp [rank]
  have hrest (i : K) : rank i.val = r i := by
    have hi : i.val ≠ leaf := by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using i.property
    simp only [rank,dite_eq_right hi]
    exact congrArg r (Subtype.ext rfl)
  have hlast (i : I) (hi : i ≠ leaf) : rank i < rank leaf := by
    rw [hleaf]
    simpa only [rank,dite_eq_right hi] using hcap ⟨i,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hi⟩
  have hinj : Function.Injective rank := by
    intro i j he
    by_cases hi : i = leaf
    · subst i
      by_cases hj : j = leaf
      · exact hj.symm
      · exact (Nat.ne_of_lt (hlast j hj) he.symm).elim
    · by_cases hj : j = leaf
      · subst j
        exact (Nat.ne_of_lt (hlast i hi) he).elim
      · have h := hr.1 (show r ⟨i,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hi⟩ = r ⟨j,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hj⟩ by
          simpa only [rank,dite_eq_right hi,dite_eq_right hj] using he)
        exact congrArg Subtype.val h
  have hprevious (i : K) :
      (⋃ j : {j : I // rank j < rank i.val}, F j.val) =
        (⋃ j : {j : K // r j < r i}, F j.val.val) := by
    ext x
    constructor
    · intro hx
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
      have hjne : j.val ≠ leaf := by
        intro he
        have hji := j.property
        rw [he] at hji
        have hil := hlast i.val (by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using i.property)
        omega
      let j' : K := ⟨j.val,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hjne⟩
      have hji : r j' < r i := by
        rw [← hrest j',← hrest i]
        exact j.property
      exact Set.mem_iUnion.mpr ⟨⟨j',hji⟩,hj⟩
    · intro hx
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
      have hji : rank j.val.val < rank i.val := by
        rw [hrest,hrest]
        exact j.property
      exact Set.mem_iUnion.mpr ⟨⟨j.val.val,hji⟩,hj⟩
  refine ⟨rank,⟨hinj,?_⟩,hlast⟩
  intro i ⟨j,hji⟩
  by_cases hi : i = leaf
  · subst i
    refine ⟨parent,hlast parent hpne,?_⟩
    apply Set.Subset.antisymm
    · rintro x ⟨hxl,hx⟩
      obtain ⟨k,hxk⟩ := Set.mem_iUnion.mp hx
      have hkne : k.val ≠ leaf := by
        intro he
        have hkl := k.property
        rw [he] at hkl
        exact (Nat.lt_irrefl _ hkl)
      exact ⟨hxl,J.mem_parent_of_mem_leaf_and_other hadj huniq hkne hxl hxk⟩
    · rintro x ⟨hxl,hxp⟩
      exact ⟨hxl,Set.mem_iUnion.mpr ⟨⟨parent,hlast parent hpne⟩,hxp⟩⟩
  · let i' : K := ⟨i,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hi⟩
    have hjne : j ≠ leaf := by
      intro he
      rw [he] at hji
      have := hlast i hi
      omega
    let j' : K := ⟨j,by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hjne⟩
    have hjr : r j' < r i' := by
      rw [← hrest j',← hrest i']
      exact hji
    obtain ⟨q,hq,htrace⟩ := hr.2 i' ⟨j',hjr⟩
    refine ⟨q.val,?_,?_⟩
    · change rank q.val < rank i'.val
      rw [hrest,hrest]
      exact hq
    · change F i'.val ∩ (⋃ k : {k // rank k < rank i'.val}, F k.val) =
        F i'.val ∩ F q.val
      rw [hprevious i']
      exact htrace

end ContactJoinTree

/-- A finite nonempty family has a join tree exactly when it admits an
injective admissible ranking, including the preceding-union equalities. -/
theorem contact_joinTree_iff_admissibleRank [Fintype I] [Nonempty I]
    (F : I → Set W) :
    Nonempty (ContactJoinTree F) ↔ ∃ rank : I → ℕ, ContactAdmissibleRank F rank := by
  constructor
  · rintro ⟨J⟩
    let root := Classical.choice (inferInstance : Nonempty I)
    exact ⟨J.parentFirstRank root,J.parentFirstRank_admissible root⟩
  · rintro ⟨rank,hrank⟩
    exact contact_joinTree_of_admissibleRank F rank hrank

end StructuralRamsey.Girth

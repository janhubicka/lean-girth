import Girth.ContactTraceTreeStep
import Girth.ContactJoinTree

/-! Unfold a finite tree of traces into fresh full copies. Equalities on
the selected vertex set are retained; all retained identifications map
back to genuine equalities in the original ambient structure. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W I : Type v}

theorem contact_trace_tree_unfold
    {A : RelStructure L U} {B : RelStructure L V} {C : RelStructure L W}
    {I : Type v}
    [Fintype I] [Nonempty I] (b : I → Embedding B C) (Z : Set W)
    (J : ContactJoinTree (fun i => Z ∩ copyCarrier (b i)))
    (hOverlap : PairwiseSupportedBCopyOverlap A b) :
    ∃ (X : Type v) (T : RelStructure L X), ContactFreeTree A B X T ∧
      ∃ (p : X → W) (e : I → Embedding B T),
        T.IsHomomorphism C p ∧ (∀ i x, p (e i x) = b i x) ∧
        (∀ i j x y, b i x = b j y → b i x ∈ Z → e i x = e j y) := by
  classical
  by_cases hsub : Subsingleton I
  · letI : Subsingleton I := hsub
    let i : I := Classical.choice inferInstance
    refine ⟨V,B,.copy (Iso.refl B),b i,fun _ => (Iso.refl B).toEmbedding,?_,?_,?_⟩
    · intro R z hz
      exact ((b i).map_rel_iff R z).mpr hz
    · intro j x
      change b i x = b j x
      rw [Subsingleton.elim j i]
    · intro j k x y hxy _
      change x = y
      apply (b i).injective
      simpa only [Subsingleton.elim j i,Subsingleton.elim k i] using hxy
  · letI : Nontrivial I := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨leaf,parent,hadj,huniq,_⟩ := J.exists_leaf_attachment
    let I' := {i : I // i ∈ ({leaf} : Set I)ᶜ}
    let parent' : I' := ⟨parent,by simpa using hadj.ne.symm⟩
    letI : Nonempty I' := ⟨parent'⟩
    have hcard : Fintype.card I' < Fintype.card I := by
      apply Fintype.card_lt_of_injective_not_surjective (fun i : I' => i.val)
        Subtype.val_injective
      intro hsurj
      obtain ⟨i,hi⟩ := hsurj leaf
      exact (show i.val ≠ leaf by
        simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using i.property) hi
    let b' : I' → Embedding B C := fun i => b i.val
    have hRest : PairwiseSupportedBCopyOverlap A b' := by
      intro i j hij
      exact hOverlap (fun he => hij (Subtype.ext he))
    obtain ⟨X,T,hT,p,e,hp,he,htrace⟩ := contact_trace_tree_unfold (I := I') b' Z
      (J.eraseLeaf hadj huniq) hRest
    obtain ⟨Y,S,hS,i₀,i₁,q,hq,hq₀,hq₁,halign⟩ :=
      contact_trace_attach hT (b parent) (b leaf) (hOverlap hadj.ne.symm)
        (e parent') p hp (he parent')
    let f (i : I) : Embedding B S := if h : i = leaf then i₁
      else i₀.comp (e ⟨i,by simpa using h⟩)
    have hfLeaf : f leaf = i₁ := by simp [f]
    have hfOther (i : I) (hi : i ≠ leaf) :
        f i = i₀.comp (e ⟨i,by simpa using hi⟩) := by simp [f,hi]
    have hLeafOther (j : I) (hj : j ≠ leaf) (x y : V)
        (hxy : b leaf x = b j y) (hz : b leaf x ∈ Z) : f leaf x = f j y := by
      have hpar : b leaf x ∈ Z ∩ copyCarrier (b parent) :=
        J.mem_parent_of_mem_leaf_and_other hadj huniq hj
          ⟨hz,⟨x,rfl⟩⟩ ⟨hz,⟨y,hxy.symm⟩⟩
      obtain ⟨z,hzpar⟩ := hpar.2
      have ht : e parent' z = e ⟨j,by simpa using hj⟩ y :=
        htrace parent' ⟨j,by simpa using hj⟩ z y (hzpar.trans hxy) (hzpar ▸ hz)
      rw [hfLeaf,hfOther j hj]
      change i₁ x = i₀ (e ⟨j,by simpa using hj⟩ y)
      exact (halign z x hzpar).symm.trans (congrArg i₀ ht)
    refine ⟨Y,S,hS,q,f,hq,?_,?_⟩
    · intro i x
      by_cases hi : i = leaf
      · subst i
        rw [hfLeaf]
        exact hq₁ x
      · rw [hfOther i hi]
        exact (hq₀ _).trans (he _ _)
    · intro i j x y hxy hz
      by_cases hi : i = leaf
      · subst i
        by_cases hj : j = leaf
        · subst j
          exact congrArg (f leaf) ((b leaf).injective hxy)
        · exact hLeafOther j hj x y hxy hz
      · by_cases hj : j = leaf
        · subst j
          exact (hLeafOther i hi y x hxy.symm (hxy ▸ hz)).symm
        · rw [hfOther i hi,hfOther j hj]
          exact congrArg i₀ (htrace ⟨i,by simpa using hi⟩ ⟨j,by simpa using hj⟩ x y hxy hz)
termination_by Fintype.card I
decreasing_by exact hcard

/-- A trace join tree yields the desired induced embedding as soon as
its full B-copies cover the vertices and every ambient relation tuple on Z.
The latter includes nullary tuples and makes the empty-Z case explicit. -/
theorem contact_trace_tree_embeds_supported
    {A : RelStructure L U} {B : RelStructure L V} {C : RelStructure L W}
    [Fintype I] [Nonempty I] (b : I → Embedding B C) (Z : Set W)
    (J : ContactJoinTree (fun i => Z ∩ copyCarrier (b i)))
    (hOverlap : PairwiseSupportedBCopyOverlap A b)
    (hcover : ∀ x ∈ Z, ∃ i, x ∈ copyCarrier (b i))
    (hrel : ∀ R (z : Fin (L.arity R) → W), C.rel R z →
      (∀ k, z k ∈ Z) → ∃ i, ∀ k, z k ∈ copyCarrier (b i))
    (α : Embedding A B) (a₀ a₁ : U) (hne : a₀ ≠ a₁) :
    ∃ (X : Type v) (T : RelStructure L X) (e : Embedding (C.induce Z) T),
      ASupportedTreeAmalgam A B X T := by
  classical
  obtain ⟨X,T,hT,p,e,hp,he,htrace⟩ := contact_trace_tree_unfold b Z J hOverlap
  have hx (z : Z) : ∃ i x, b i x = z.val := by
    obtain ⟨i,x,hx⟩ := hcover z.val z.property
    exact ⟨i,x,hx⟩
  choose index pos hpos using hx
  let f (z : Z) : X := e (index z) (pos z)
  have hleft (z : Z) : p (f z) = z.val := (he _ _).trans (hpos z)
  have hagree (z : Z) (i : I) (x : V) (h : b i x = z.val) : f z = e i x :=
    htrace (index z) i (pos z) x ((hpos z).trans h.symm) ((hpos z) ▸ z.property)
  let emb : Embedding (C.induce Z) T := {
    toFun := f
    injective := by
      intro x y hxy
      apply Subtype.ext
      exact (hleft x).symm.trans ((congrArg p hxy).trans (hleft y))
    map_rel_iff := by
      intro R z
      constructor
      · intro hz
        have h := hp R (f ∘ z) hz
        have hfun : p ∘ (f ∘ z) = Subtype.val ∘ z := funext (fun k => hleft (z k))
        rw [hfun] at h
        exact h
      · intro hz
        obtain ⟨i,hi⟩ := hrel R (Subtype.val ∘ z) hz (fun k => (z k).property)
        choose x hx using hi
        have hfun : b i ∘ x = Subtype.val ∘ z := funext hx
        have hxrel : B.rel R x := (b i).map_rel_iff R x |>.mp (hfun ▸ hz)
        have hmap : e i ∘ x = f ∘ z := funext (fun k => (hagree (z k) i (x k) (hx k)).symm)
        exact hmap ▸ ((e i).map_rel_iff R x).mpr hxrel }
  obtain ⟨Y,S,g,hS⟩ := hT.embeds_supportedTree α a₀ a₁ hne
  exact ⟨Y,S,g.comp emb,hS⟩

end StructuralRamsey.Girth

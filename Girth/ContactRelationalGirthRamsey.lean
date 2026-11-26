import Girth.ContactRelationalSupportWitness

/-! End-to-end relational theorem. The mixed completion is stated
on actual ambient embeddings, not on abstract designated labels.
The finite equivalences transport the same selected family, tree
and sharp number of extra B-members. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W F J : Type v}

def contactActualMember {A : RelStructure L U} {B : RelStructure L V}
    {C : RelStructure L W} :
    (Embedding B C ⊕ Embedding A C) → ABMember A B C
  | .inl b => .b b
  | .inr a => .a a

open Classical in
/-- The quantitative mixed completion property on actual relational
copies, including a singleton family with no added member. -/
def ContactActualMixedCompletion (A : RelStructure L U) (B : RelStructure L V)
    (C : RelStructure L W) (g n : ℕ) : Prop :=
  ∀ s : Finset (Embedding B C ⊕ Embedding A C), s.Nonempty → s.card ≤ n →
    ∃ t : Finset (Embedding B C ⊕ Embedding A C), s ⊆ t ∧
      (∀ a ∈ t, a ∉ s → ∃ b : Embedding B C, a = Sum.inl b) ∧
      (s.card = 1 → t = s) ∧
      (g-1)*(t \ s).card ≤ s.card-2 ∧
      ForestOfCopies (fun a : {a // a ∈ t} =>
        (contactActualMember a.val).supportPiece A) ∧
      ∃ (X : Type v) (D : RelStructure L X)
        (e : Embedding (mixedFamilyUnionStructure C
          (fun a : {a // a ∈ t} => contactActualMember a.val)) D),
        ASupportedTreeAmalgam A B X D

namespace ContactRelationalRealization
variable {A : RelStructure L U} {B : RelStructure L V}
    {H : ContactHypergraphData W F J} (R : ContactRelationalRealization A B H)

theorem edge_eq_symm (a : Embedding A R.ambient) :
    H.edgeCarrier (R.edge.symm a) = copyCarrier a := by
  rw [← R.edge_eq,R.edge.apply_symm_apply]

theorem copy_eq_symm (b : Embedding B R.ambient) :
    H.copyCarrier (R.copy.symm b) = copyCarrier b := by
  rw [← R.copy_eq,R.copy.apply_symm_apply]

theorem all_AStrong (hpair : H.bottomCut.ZeroPairwise) :
    ∀ b : Embedding B R.ambient, AStrong A R.ambient (copyCarrier b) := by
  intro b a hne
  let e := R.edge.symm a
  let j := R.copy.symm b
  have he : H.edgeCarrier e = copyCarrier a := R.edge_eq_symm a
  have hj : H.copyCarrier j = copyCarrier b := R.copy_eq_symm b
  rw [← he,← hj] at hne ⊢
  rcases hpair (Sum.inr e) (Sum.inl j) (by simp) with hs | ⟨f,hf,_,hEq⟩
  · exact (hne hs).elim
  · change f = e at hf
    subst f
    change H.edgeCarrier e ∩ H.copyCarrier j = H.edgeCarrier e at hEq
    intro x hx
    exact (show x ∈ H.edgeCarrier e ∩ H.copyCarrier j from hEq.symm ▸ hx).2

theorem BIntersections (hpair : H.bottomCut.ZeroPairwise) :
    BIntersectionsControlled A B R.ambient := by
  intro b c hne
  let i := R.copy.symm b
  let j := R.copy.symm c
  have hi : H.copyCarrier i = copyCarrier b := R.copy_eq_symm b
  have hj : H.copyCarrier j = copyCarrier c := R.copy_eq_symm c
  have hn : i ≠ j := by
    intro h
    exact hne (hi.symm.trans ((congrArg H.copyCarrier h).trans hj))
  rw [← hi,← hj]
  rcases hpair (Sum.inl i) (Sum.inl j) (fun h => hn (Sum.inl.inj h)) with hs | ⟨e,_,_,he⟩
  · exact Or.inl hs
  · exact Or.inr ⟨R.edge e,he.trans (R.edge_eq e).symm⟩

theorem BSingletonSupported (h : H.MixedSharedSupported) :
    BSingletonIntersectionsSupported A B R.ambient := by
  intro b c hne _ x hx
  let i := R.copy.symm b
  let j := R.copy.symm c
  have hi : H.copyCarrier i = copyCarrier b := R.copy_eq_symm b
  have hj : H.copyCarrier j = copyCarrier c := R.copy_eq_symm c
  have hn : i ≠ j := by
    intro he
    exact hne (hi.symm.trans ((congrArg H.copyCarrier he).trans hj))
  obtain ⟨⟨e,he,he'⟩,⟨f,hf,hf'⟩⟩ :=
    h (Sum.inl i) (Sum.inl j) (fun he => hn (Sum.inl.inj he)) x
      (hi.symm ▸ hx.1) (hj.symm ▸ hx.2)
  constructor
  · refine ⟨R.edge e,?_,?_⟩
    · rw [R.edge_eq]; exact he
    · rw [R.edge_eq,← hi]; exact he'
  · refine ⟨R.edge f,?_,?_⟩
    · rw [R.edge_eq]; exact hf
    · rw [R.edge_eq,← hj]; exact hf'

/-- Transport the finite mixed family by the actual label
equivalence. The difference of cardinalities, hence the
completion budget, is unchanged by this transport. -/
theorem actualCompletion (g n : ℕ)
    (hQ : H.QuantitativeCompletion g n)
    (hpair : H.bottomCut.ZeroPairwise)
    (hShared : H.MixedSharedSupported)
    (α : Embedding A B) (a₀ a₁ : U) (hne : a₀ ≠ a₁) :
    ContactActualMixedCompletion A B R.ambient g n := by
  classical
  intro s hs hsc
  let e := R.mixedEquiv
  let s₀ : Finset (J ⊕ F) := s.map e.symm.toEmbedding
  have hS (i : J ⊕ F) : i ∈ s₀ ↔ e i ∈ s := by
    constructor
    · intro hi
      obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hi
      change e.symm a = i at he
      rw [← he,e.apply_symm_apply]
      exact ha
    · intro hi
      exact Finset.mem_map.mpr ⟨e i,hi,e.symm_apply_apply i⟩
  have hs₀ : s₀.Nonempty := by
    obtain ⟨a,ha⟩ := hs
    exact ⟨e.symm a,(hS _).mpr (by rw [e.apply_symm_apply]; exact ha)⟩
  have hsc₀ : s₀.card = s.card := by simp [s₀]
  have aux : ∃ t₀ : Finset (J ⊕ F), s₀ ⊆ t₀ ∧
      (∀ a ∈ t₀, a ∉ s₀ → ∃ j : J, a = Sum.inl j) ∧
      (s.card = 1 → t₀ = s₀) ∧ (g-1)*(t₀ \ s₀).card ≤ s₀.card-2 ∧
      Nonempty (ContactJoinTree (fun a : {a // a ∈ t₀} => H.bottomCut.carrier a.val)) := by
    by_cases htwo : 2 ≤ s₀.card
    · obtain ⟨t,ht,hadd,hJ,hcost⟩ := hQ s₀ htwo (by rw [hsc₀]; exact hsc)
      exact ⟨t,ht,hadd,fun h => (by omega : False).elim,hcost,hJ⟩
    · have hpos := Finset.card_pos.mpr hs₀
      have hone : s₀.card = 1 := by omega
      obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hone
      let K := {a : J ⊕ F // a ∈ s₀}
      letI : Nonempty K := by
        obtain ⟨i,hi⟩ := hs₀
        exact ⟨⟨i,hi⟩⟩
      letI : Subsingleton K := ⟨by
        intro i j
        have hi := i.property
        have hj := j.property
        rw [ha] at hi hj
        exact Subtype.ext ((Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm)⟩
      exact ⟨s₀,Finset.Subset.rfl,fun _ h hn => (hn h).elim,fun _ => rfl,
        by simp,⟨ContactJoinTree.of_subsingleton _⟩⟩
  obtain ⟨t₀,hst₀,hadd,hSingle,hcost,⟨T⟩⟩ := aux
  let t := t₀.map e.toEmbedding
  have hT (i : J ⊕ F) : i ∈ t₀ ↔ e i ∈ t := by
    constructor
    · intro hi
      exact Finset.mem_map.mpr ⟨i,hi,rfl⟩
    · intro hi
      obtain ⟨j,hj,hji⟩ := Finset.mem_map.mp hi
      have he : j = i := e.injective hji
      exact he ▸ hj
  have hst : s ⊆ t := by
    intro a ha
    have h := (hS (e.symm a)).mpr (by rw [e.apply_symm_apply]; exact ha)
    have h' := (hT _).mp (hst₀ h)
    rwa [e.apply_symm_apply] at h'
  have htc : t.card = t₀.card := by simp [t]
  have hDiff : (t \ s).card = (t₀ \ s₀).card := by
    have h₁ := Finset.card_sdiff_add_card_eq_card hst
    have h₂ := Finset.card_sdiff_add_card_eq_card hst₀
    omega
  let r (a : {a // a ∈ t}) : {i // i ∈ t₀} :=
    ⟨e.symm a.val,(hT _).mpr (by rw [e.apply_symm_apply]; exact a.property)⟩
  have hri : Function.Injective r := by
    intro a b he
    exact Subtype.ext (e.symm.injective (congrArg Subtype.val he))
  have hrs : Function.Surjective r := by
    intro i
    refine ⟨⟨e i.val,(hT _).mp i.property⟩,?_⟩
    exact Subtype.ext (e.symm_apply_apply i.val)
  let er := Equiv.ofBijective r ⟨hri,hrs⟩
  let sel : {a // a ∈ t} ↪ (J ⊕ F) :=
    er.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  let T' : ContactJoinTree (fun a : {a // a ∈ t} => H.bottomCut.carrier (sel a)) :=
    T.reindex er
  have hEq : (fun a : {a // a ∈ t} => R.member (sel a)) =
      (fun a : {a // a ∈ t} => contactActualMember a.val) := by
    funext a
    change R.actualMember (e (e.symm a.val)) = contactActualMember a.val
    rw [e.apply_symm_apply]
    rfl
  letI : Nonempty {a // a ∈ t} := by
    obtain ⟨a,ha⟩ := hs
    exact ⟨⟨a,hst ha⟩⟩
  refine ⟨t,hst,?_,?_,?_,?_,?_⟩
  · intro a ha hn
    let i := e.symm a
    have hi := (hT i).mpr (by rw [e.apply_symm_apply]; exact ha)
    have hi' : i ∉ s₀ := by
      intro hs
      have h := (hS i).mp hs
      rw [e.apply_symm_apply] at h
      exact hn h
    obtain ⟨j,hj⟩ := hadd i hi hi'
    refine ⟨R.copy j,?_⟩
    have h := congrArg e hj
    change e (e.symm a) = e (Sum.inl j) at h
    rw [e.apply_symm_apply] at h
    exact h
  · intro h
    have he := hSingle h
    ext a
    have h₁ := hT (e.symm a)
    have h₂ := hS (e.symm a)
    rw [e.apply_symm_apply] at h₁ h₂
    rw [he] at h₁
    exact h₁.symm.trans h₂
  · rw [hDiff,← hsc₀]
    exact hcost
  · have h := R.mixedForest_of_joinTree sel hpair T'
    have h' := congrArg (fun f : {a // a ∈ t} → ABMember A B R.ambient =>
      ForestOfCopies (fun k => (f k).supportPiece A)) hEq
    exact h' ▸ h
  · have h := R.mixedTree_of_joinTree sel hpair hShared T' α a₀ a₁ hne
    rw [hEq] at h
    exact h

end ContactRelationalRealization

/-- Relational local-tree girth Ramsey theorem (the circulation
statement). The ambient order relation is a subrelation of the
displayed linear order, NOT the completed order. The quantified
mixed families use actual embeddings of the rigid ordered sources. -/
theorem contactRelationalGirthRamsey
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] [Fintype U] [Finite V]
    (ha : 2 ≤ Fintype.card U) (α : Embedding A.ordered B.ordered)
    (g n : ℕ) (hg : 2 ≤ g) (hn : 2 ≤ n)
    (hG : GirthGT (supportCopies A.ordered B.ordered) g)
    (Color : Type v) [Finite Color] [Nonempty Color] :
    ∃ (W : Type v) (C : RelStructure L.withOrder W) (o : LinearOrder W),
      Finite W ∧ @RelStructure.ExtendsOrder L W C o.toLT ∧
      StructuralRamsey.Arrow A.ordered B.ordered C Color ∧
      (∀ T : Set W, (C.induce T).Irreducible →
        ∃ b : Embedding B.ordered C, T ⊆ copyCarrier b) ∧
      ContactActualMixedCompletion A.ordered B.ordered C g n ∧
      GirthGT (supportCopies A.ordered C) g ∧
      (∀ b : Embedding B.ordered C, AStrong A.ordered C (copyCarrier b)) ∧
      BIntersectionsControlled A.ordered B.ordered C ∧
      BSingletonIntersectionsSupported A.ordered B.ordered C := by
  classical
  let m := max 3 (max g n)
  have hm : 2 ≤ m := by omega
  have hgm : g ≤ m := by exact le_trans (le_max_left g n) (le_max_right 3 (max g n))
  have hnm : n ≤ m := by exact le_trans (le_max_right g n) (le_max_right 3 (max g n))
  have h3m : 3 ≤ m := le_max_left 3 (max g n)
  letI : Nontrivial U := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨W⟩ := contactRelationalSupportWitness_exists A B ha α g m hg hm hG Color
  letI : Finite W.Vertex := W.finiteV
  letI : Fintype W.Vertex := Fintype.ofFinite _
  letI : LinearOrder W.Vertex := W.order
  letI : Nonempty W.Copy := by
    obtain ⟨j,_,_⟩ := W.arrow (fun _ => Classical.choice (inferInstance : Nonempty Color))
    exact ⟨j⟩
  have hlin := W.graph.linear_of_pairwise W.pairwise
  have hconf : ContactConformal W.graph.copyCarrier :=
    contact_conformal_of_threeCompletable W.graph.copyCarrier
      (fun s hs hcard => W.completable s hs (hcard.trans h3m))
  have hsource := contactRelationalTarget_girth hG
  have hQ : W.graph.QuantitativeCompletion g m := by
    intro s hs hsm
    exact W.graph.bottomCut.mixedCompletion_cost g m hg hlin W.pairwise W.covered.2
      W.family.copy_edge_subset_from_embeddings (W.family.copy_girth_of_source hsource)
      W.completable s hs hsm
  have hHg := W.graph.girth_of_quantitativeCompletion g m hg hgm hlin hQ
  obtain ⟨R,horder,_,hcomp,hcover⟩ := contactRealizeSupport W.family W.emb_order
    W.diagonal W.covered.1 W.covered.2 hconf W.pairwise hlin W.distinct
  obtain ⟨a₀,a₁,hne⟩ := exists_pair_ne U
  have hQn : W.graph.QuantitativeCompletion g n :=
    fun s hs hc => hQ s hs (hc.trans hnm)
  refine ⟨W.Vertex,R.ambient,W.order,W.finiteV,horder,
    R.arrow W.family hcomp W.arrow,?_,
    R.actualCompletion g n hQn W.pairwise W.shared α a₀ a₁ hne,
    R.girth hHg,R.all_AStrong W.pairwise,R.BIntersections W.pairwise,
    R.BSingletonSupported W.shared⟩
  intro T hT
  obtain ⟨j,hj⟩ := hcover T hT
  exact ⟨R.copy j,hj⟩

end StructuralRamsey.Girth

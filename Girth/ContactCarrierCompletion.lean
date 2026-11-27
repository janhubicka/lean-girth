import Girth.ContactRelationalGirthRamsey

/-! Translate the tagged-embedding statement into the manuscript's
unambiguous set-family convention. In particular, when A and B
are isomorphic, the same carrier is not counted twice. Choose the
B-tag whenever it is available. Since added labels are always
B-tags, the completed family retains this canonical choice. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W : Type v}

namespace ContactActualCarrier
variable {A : RelStructure L U} {B : RelStructure L V} {C : RelStructure L W}

abbrev Label (A : RelStructure L U) (B : RelStructure L V) (C : RelStructure L W) :=
  Embedding B C ⊕ Embedding A C

def carrier (a : Label A B C) : Set W := (contactActualMember a).carrier

def Canonical (a : Label A B C) : Prop :=
  match a with
  | .inl _ => True
  | .inr a => ¬ ∃ b : Embedding B C, copyCarrier b = copyCarrier a

theorem exists_canonical (X : Set W) (hX : X ∈ Set.range (carrier (A := A) (B := B) (C := C))) :
    ∃ a : Label A B C, Canonical a ∧ carrier a = X := by
  classical
  by_cases hB : ∃ b : Embedding B C, copyCarrier b = X
  · obtain ⟨b,hb⟩ := hB
    exact ⟨Sum.inl b,True.intro,hb⟩
  obtain ⟨a,ha⟩ := hX
  cases a with
  | inl b => exact (hB ⟨b,ha⟩).elim
  | inr a =>
    refine ⟨Sum.inr a,?_,ha⟩
    intro h
    obtain ⟨b,hb⟩ := h
    exact hB ⟨b,hb.trans ha⟩

/-- With rigid ordered sources the canonical labels inject into
the carrier sets, including when the source structures coincide. -/
theorem canonical_injective
    {A₀ : RelStructure L U} {B₀ : RelStructure L V}
    {C₀ : RelStructure L.withOrder W}
    [Finite U] [Finite V] [LinearOrder U] [LinearOrder V] [LinearOrder W]
    (hC : C₀.ExtendsOrder)
    {a b : Label A₀.ordered B₀.ordered C₀}
    (ha : Canonical a) (hb : Canonical b) (he : carrier a = carrier b) :
    a = b := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (contact_ordered_embedding_eq hC a b he)
    | inr b => exact (hb ⟨a,he⟩).elim
  | inr a =>
    cases b with
    | inl b => exact (ha ⟨b,he.symm⟩).elim
    | inr b => exact congrArg Sum.inr (contact_ordered_embedding_eq hC a b he)

end ContactActualCarrier

open ContactActualCarrier

open Classical in
/-- Actual carrier-set version of the manuscript's completion.
Each member of the completed set family has its actual relational
realization. The budget counts DIFFERENT added carrier sets. -/
def ContactCarrierMixedCompletion (A : RelStructure L U) (B : RelStructure L V)
    (C : RelStructure L W) (g n : ℕ) : Prop :=
  ∀ s : Finset (Set W), s.Nonempty → s.card ≤ n →
    (∀ X ∈ s, X ∈ Set.range (carrier (A := A) (B := B) (C := C))) →
    ∃ t : Finset (Set W), s ⊆ t ∧
      (∀ X ∈ t, X ∉ s → ∃ b : Embedding B C, copyCarrier b = X) ∧
      (s.card = 1 → t = s) ∧ (g-1)*(t \ s).card ≤ s.card-2 ∧
      ∃ m : {X // X ∈ t} → ABMember A B C,
        (∀ X, (m X).carrier = X.val) ∧
        ForestOfCopies (fun X => (m X).supportPiece A) ∧
        ∃ (Y : Type v) (D : RelStructure L Y)
          (e : Embedding (mixedFamilyUnionStructure C m) D),
          ASupportedTreeAmalgam A B Y D

/-- Reindexing a generated mixed union only changes the indexing,
not its carrier or relational tuples. -/
def contactMixedUnion_reindex
    {A : RelStructure L U} {B : RelStructure L V} {C : RelStructure L W}
    {I J : Type v} (m : I → ABMember A B C) (e : J ≃ I) :
    Embedding (mixedFamilyUnionStructure C (fun j => m (e j)))
      (mixedFamilyUnionStructure C m) where
  toFun x := ⟨x.val,by
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp x.property
    exact Set.mem_iUnion.mpr ⟨e j,hj⟩⟩
  injective := fun x y h => Subtype.ext
    (congrArg (fun z : mixedFamilyCarrier m => z.val) h)
  map_rel_iff := by
    intro R x
    constructor
    · rintro ⟨hx,i,hi⟩
      refine ⟨hx,e.symm i,?_⟩
      intro k
      change (x k).val ∈ (m (e (e.symm i))).carrier
      rw [e.apply_symm_apply]
      exact hi k
    · rintro ⟨hx,j,hj⟩
      exact ⟨hx,e j,hj⟩

theorem contactCarrierMixedCompletion_of_actual
    {A : RelStructure L U} {B : RelStructure L V} {C : RelStructure L.withOrder W}
    [Finite U] [Finite V] [LinearOrder U] [LinearOrder V] [LinearOrder W]
    (hC : C.ExtendsOrder) (g n : ℕ)
    (h : ContactActualMixedCompletion A.ordered B.ordered C g n) :
    ContactCarrierMixedCompletion A.ordered B.ordered C g n := by
  classical
  intro s hs hn hsrc
  let K := Label A.ordered B.ordered C
  let c : K → Set W := carrier
  have hex (X : {X : Set W // X ∈ s}) : ∃ a : K, Canonical a ∧ c a = X.val :=
    exists_canonical X.val (hsrc _ X.property)
  let a (X : {X : Set W // X ∈ s}) : K := Classical.choose (hex X)
  have ha (X : {X : Set W // X ∈ s}) : Canonical (a X) ∧ c (a X) = X.val :=
    Classical.choose_spec (hex X)
  have hai : Function.Injective a := by
    intro X Y he
    apply Subtype.ext
    rw [← (ha X).2,← (ha Y).2,he]
  let ae : {X : Set W // X ∈ s} ↪ K := ⟨a,hai⟩
  let s₀ : Finset K := s.attach.map ae
  have hsc : s₀.card = s.card := by simp [s₀]
  have hs₀ : s₀.Nonempty := by
    obtain ⟨X,hX⟩ := hs
    exact ⟨a ⟨X,hX⟩,Finset.mem_map.mpr ⟨⟨X,hX⟩,Finset.mem_attach _ _,rfl⟩⟩
  obtain ⟨t₀,hst,hadd,hsingle,hbudget,hforest,hUnion⟩ :=
    h s₀ hs₀ (by rw [hsc]; exact hn)
  have hc (b : K) (hb : b ∈ t₀) : Canonical b := by
    by_cases hmem : b ∈ s₀
    · obtain ⟨X,_,hX⟩ := Finset.mem_map.mp hmem
      change a X = b at hX
      exact hX ▸ (ha X).1
    · obtain ⟨d,hd⟩ := hadd b hb hmem
      rw [hd]
      exact True.intro
  let f : {b : K // b ∈ t₀} ↪ Set W := {
    toFun := fun b => c b.val
    inj' := fun b d he => Subtype.ext
      (canonical_injective hC (hc _ b.property) (hc _ d.property) he) }
  let t : Finset (Set W) := t₀.attach.map f
  have htc : t.card = t₀.card := by simp [t]
  have hst' : s ⊆ t := by
    intro X hX
    let z : {X : Set W // X ∈ s} := ⟨X,hX⟩
    have hz : a z ∈ s₀ := Finset.mem_map.mpr ⟨z,Finset.mem_attach _ _,rfl⟩
    exact Finset.mem_map.mpr ⟨⟨a z,hst hz⟩,Finset.mem_attach _ _,(ha z).2⟩
  have hdif : (t \ s).card = (t₀ \ s₀).card := by
    have h₁ := Finset.card_sdiff_add_card_eq_card hst'
    have h₂ := Finset.card_sdiff_add_card_eq_card hst
    omega
  let f' (b : {b : K // b ∈ t₀}) : {X : Set W // X ∈ t} :=
    ⟨f b,Finset.mem_map.mpr ⟨b,Finset.mem_attach _ _,rfl⟩⟩
  have hfi : Function.Injective f' := fun b d he => f.injective (congrArg Subtype.val he)
  have hfs : Function.Surjective f' := by
    intro X
    obtain ⟨b,_,he⟩ := Finset.mem_map.mp X.property
    exact ⟨b,Subtype.ext he⟩
  let e := (Equiv.ofBijective f' ⟨hfi,hfs⟩).symm
  let m₀ (b : {b : K // b ∈ t₀}) : ABMember A.ordered B.ordered C :=
    contactActualMember b.val
  let m (X : {X : Set W // X ∈ t}) := m₀ (e X)
  have hm (X : {X : Set W // X ∈ t}) : (m X).carrier = X.val := by
    exact congrArg Subtype.val (e.symm_apply_apply X)
  refine ⟨t,hst',?_,?_,?_,m,hm,?_,?_⟩
  · intro X hX hnot
    obtain ⟨b,_,hb⟩ := Finset.mem_map.mp hX
    have hb' : b.val ∉ s₀ := by
      intro hmem
      obtain ⟨Y,_,hY⟩ := Finset.mem_map.mp hmem
      change a Y = b.val at hY
      have he : c b.val = Y.val := hY ▸ (ha Y).2
      have he' : c b.val = X := hb
      exact hnot (he.symm.trans he' ▸ Y.property)
    obtain ⟨d,hd⟩ := hadd b.val b.property hb'
    have hcarrier : c b.val = copyCarrier d := congrArg c hd
    exact ⟨d,hcarrier.symm.trans (show c b.val = X from hb)⟩
  · intro h1
    have he := hsingle (hsc.trans h1)
    apply Finset.Subset.antisymm ?_ hst'
    intro X hX
    obtain ⟨b,_,hb⟩ := Finset.mem_map.mp hX
    have hs' : b.val ∈ s₀ := he ▸ b.property
    obtain ⟨Y,_,hY⟩ := Finset.mem_map.mp hs'
    change a Y = b.val at hY
    have hh : c b.val = Y.val := hY ▸ (ha Y).2
    exact hh.symm.trans (show c b.val = X from hb) ▸ Y.property
  · rw [hdif,← hsc]
    exact hbudget
  · refine ⟨?_,?_⟩
    · intro X Y hne
      exact hforest.1 (fun he => hne (e.injective he))
    · rcases hforest.2 with hEmpty | hTree
      · exact Or.inl ⟨fun X => hEmpty.false (e X)⟩
      · obtain ⟨T⟩ := hTree
        exact Or.inr ⟨T.reindex e⟩
  · obtain ⟨Y,D,hEmb,hD⟩ := hUnion
    exact ⟨Y,D,hEmb.comp (contactMixedUnion_reindex m₀ e),hD⟩

/-- Literal carrier-set formulation of the circulation theorem.
The result is the same ambient witness as in the tagged theorem. -/
theorem contactRelationalGirthRamsey_carriers
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
      ContactCarrierMixedCompletion A.ordered B.ordered C g n ∧
      GirthGT (supportCopies A.ordered C) g ∧
      (∀ b : Embedding B.ordered C, AStrong A.ordered C (copyCarrier b)) ∧
      BIntersectionsControlled A.ordered B.ordered C ∧
      BSingletonIntersectionsSupported A.ordered B.ordered C := by
  obtain ⟨W,C,o,hfin,hord,hArrow,hcover,hcomp,hgirth,hstrong,hinter,hshared⟩ :=
    contactRelationalGirthRamsey A B ha α g n hg hn hG Color
  letI : LinearOrder W := o
  exact ⟨W,C,o,hfin,hord,hArrow,hcover,
    contactCarrierMixedCompletion_of_actual hord g n hcomp,
    hgirth,hstrong,hinter,hshared⟩

end StructuralRamsey.Girth

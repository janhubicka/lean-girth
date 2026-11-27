import Girth.ContactCarrierCompletion
import Girth.ContactComparisonGraph

/-!
# Small induced relational substructures

The completion hypothesis concerns unions of whole copies. To pass to an
induced structure on at most n vertices, first obtain chordality on those
vertices. Simplicial elimination then covers every clique by at most one
chosen bag per vertex. Completing the corresponding B-copies includes every
relation tuple of the induced structure and gives the required embedding.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W : Type v}

/-- A finite chordal graph has a clique cover of all its nonempty
cliques using at most as many bags as vertices. -/
theorem contact_chordal_cliqueCover [Fintype W]
    (G : SimpleGraph W) (hG : ContactChordal G) :
    ∃ s : Finset (Set W), s.card ≤ Fintype.card W ∧
      (∀ K ∈ s, ContactClique G K) ∧
      (∀ K : Set W, K.Nonempty → ContactClique G K →
        ∃ T ∈ s, K ⊆ T) := by
  classical
  have aux : ∀ n : ℕ, ∀ (X : Type v) [Fintype X], Fintype.card X = n →
      ∀ H : SimpleGraph X, ContactChordal H →
      ∃ s : Finset (Set X), s.card ≤ Fintype.card X ∧
        (∀ K ∈ s, ContactClique H K) ∧
        (∀ K : Set X, K.Nonempty → ContactClique H K → ∃ T ∈ s, K ⊆ T) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X inst hn H hH
      by_cases hX : Nonempty X
      · letI : Nonempty X := hX
        obtain ⟨x,hx⟩ := contact_exists_simplicial H hH
        let Y := {y : X // y ≠ x}
        have hlt : Fintype.card Y < Fintype.card X :=
          Fintype.card_subtype_lt (x := x) (by simp)
        obtain ⟨s,hs,hcl,hcov⟩ := ih (Fintype.card Y) (by omega) Y rfl
          (H.induce {y | y ≠ x}) (contactChordal_induce hH _)
        let lift : Set Y → Set X := fun K => Subtype.val '' K
        let K₀ : Set X := {y | y = x ∨ H.Adj x y}
        have hK₀ : ContactClique H K₀ := by
          intro y hy z hz hyz
          rcases hy with rfl | hy
          · rcases hz with rfl | hz
            · exact (hyz rfl).elim
            · exact hz
          · rcases hz with rfl | hz
            · exact hy.symm
            · exact hx y z hy hz hyz
        refine ⟨insert K₀ (s.image lift),?_,?_,?_⟩
        · have h₁ := Finset.card_insert_le K₀ (s.image lift)
          have h₂ : (s.image lift).card ≤ s.card := Finset.card_image_le
          omega
        · intro K hK
          rcases Finset.mem_insert.mp hK with rfl | hK
          · exact hK₀
          · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hK
            rintro _ ⟨y,hy,rfl⟩ _ ⟨z,hz,rfl⟩ hyz
            exact hcl T hT y hy z hz (fun he => hyz (congrArg Subtype.val he))
        · intro K hK hClique
          by_cases hxK : x ∈ K
          · refine ⟨K₀,Finset.mem_insert_self _ _,?_⟩
            intro y hy
            by_cases hyx : y = x
            · exact Or.inl hyx
            · exact Or.inr (hClique x hxK y hy (fun he => hyx he.symm))
          · let K' : Set Y := {y | y.val ∈ K}
            have hK' : K'.Nonempty := by
              obtain ⟨y,hy⟩ := hK
              exact ⟨⟨y,fun he => hxK (he ▸ hy)⟩,hy⟩
            have hClique' : ContactClique (H.induce {y | y ≠ x}) K' := by
              intro y hy z hz hyz
              exact hClique y.val hy z.val hz (fun he => hyz (Subtype.ext he))
            obtain ⟨T,hT,hKT⟩ := hcov K' hK' hClique'
            refine ⟨lift T,Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨T,hT,rfl⟩),?_⟩
            intro y hy
            let y' : Y := ⟨y,fun he => hxK (he ▸ hy)⟩
            exact ⟨y',hKT hy,rfl⟩
      · letI : IsEmpty X := not_nonempty_iff.mp hX
        refine ⟨∅,by simp,?_,?_⟩
        · intro K hK
          exact (Finset.notMem_empty K hK).elim
        · intro K hK _
          obtain ⟨x,_⟩ := hK
          exact isEmptyElim x
  exact aux (Fintype.card W) W rfl G hG

/-- On a nonempty graph the same family can cover the empty clique
as well, which also handles nullary relation tuples below. -/
theorem contact_chordal_cliqueCover_nonempty [Fintype W] [Nonempty W]
    (G : SimpleGraph W) (hG : ContactChordal G) :
    ∃ s : Finset (Set W), s.Nonempty ∧ s.card ≤ Fintype.card W ∧
      (∀ K ∈ s, ContactClique G K) ∧
      (∀ K : Set W, ContactClique G K → ∃ T ∈ s, K ⊆ T) := by
  classical
  obtain ⟨s,hcard,hcl,hcov⟩ := contact_chordal_cliqueCover G hG
  let x : W := Classical.choice inferInstance
  have hsingle : ContactClique G {x} := by
    intro y hy z hz hn
    exact (hn ((Set.mem_singleton_iff.mp hy).trans (Set.mem_singleton_iff.mp hz).symm)).elim
  obtain ⟨T,hT,_⟩ := hcov {x} (Set.singleton_nonempty x) hsingle
  refine ⟨s,⟨T,hT⟩,hcard,hcl,?_⟩
  intro K hK
  by_cases hne : K.Nonempty
  · exact hcov K hne hK
  · exact ⟨T,hT,by rw [Set.not_nonempty_iff_eq_empty.mp hne]; exact Set.empty_subset _⟩

theorem contact_comparison_clique_irreducible
    (C : RelStructure L.withOrder W) (K : Set W)
    (hK : ContactClique (contactComparisonGraph C) K) :
    (C.induce K).Irreducible := by
  intro x y hn
  have h := hK x.val x.property y.val y.property (fun he => hn (Subtype.ext he))
  rcases h.2 with h | h
  · refine ⟨.inr (),?_⟩
    change ∃ (z : Fin 2 → K) (i j : Fin 2),
      (C.induce K).rel (.inr ()) z ∧ z i = x ∧ z j = y
    refine ⟨![x,y],0,1,?_,rfl,rfl⟩
    have he : Subtype.val ∘ ![x,y] = ![x.val,y.val] := by
      funext i
      fin_cases i <;> rfl
    change C.rel (.inr ()) (Subtype.val ∘ ![x,y])
    exact Eq.mpr (congrArg (fun z : Fin 2 → W => C.rel (.inr ()) z) he) h
  · refine ⟨.inr (),?_⟩
    change ∃ (z : Fin 2 → K) (i j : Fin 2),
      (C.induce K).rel (.inr ()) z ∧ z i = x ∧ z j = y
    refine ⟨![y,x],1,0,?_,rfl,rfl⟩
    have he : Subtype.val ∘ ![y,x] = ![y.val,x.val] := by
      funext i
      fin_cases i <;> rfl
    change C.rel (.inr ()) (Subtype.val ∘ ![y,x])
    exact Eq.mpr (congrArg (fun z : Fin 2 → W => C.rel (.inr ()) z) he) h

theorem contact_comparison_adj_copy
    {B : RelStructure L V} [LinearOrder V]
    {C : RelStructure L.withOrder W}
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    {x y : W} (h : (contactComparisonGraph C).Adj x y) :
    ∃ b : Embedding B.ordered C, x ∈ copyCarrier b ∧ y ∈ copyCarrier b := by
  have hK : ContactClique (contactComparisonGraph C) {x,y} := by
    intro z hz w hw hn
    rcases (Set.mem_insert_iff.mp hz) with rfl | hz
    · rcases (Set.mem_insert_iff.mp hw) with rfl | hw
      · exact (hn rfl).elim
      · have he := Set.mem_singleton_iff.mp hw
        subst w
        exact h
    · have he := Set.mem_singleton_iff.mp hz
      subst z
      rcases (Set.mem_insert_iff.mp hw) with rfl | hw
      · exact h.symm
      · have he := Set.mem_singleton_iff.mp hw
        subst w
        exact (hn rfl).elim
  obtain ⟨b,hb⟩ := hcover {x,y} (contact_comparison_clique_irreducible C {x,y} hK)
  exact ⟨b,hb (Set.mem_insert x _),hb (Set.mem_insert_of_mem _ (Set.mem_singleton y))⟩

theorem contact_mixed_member_clique
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V] {C : RelStructure L.withOrder W}
    (m : ABMember A.ordered B.ordered C) :
    ContactClique (contactComparisonGraph C) m.carrier := by
  cases m with
  | a a => exact contactComparisonGraph_embedding_ordered a
  | b b => exact contactComparisonGraph_embedding_ordered b

/-- The completed copy family supplies a chord for every comparison
cycle whose vertices lie in a set of size at most n. -/
theorem contact_small_comparison_chordal
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V] [Finite W]
    {C : RelStructure L.withOrder W} (g n : ℕ)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    (hcomp : ContactCarrierMixedCompletion A.ordered B.ordered C g n)
    (Z : Set W) (hZ : Nat.card Z ≤ n) :
    ContactChordal ((contactComparisonGraph C).induce Z) := by
  classical
  letI : Fintype W := Fintype.ofFinite _
  letI : Fintype Z := Fintype.ofFinite _
  intro k z hk hzi hs
  have hkn : k ≤ n := by
    have hh := Fintype.card_le_of_injective z hzi
    rw [Fintype.card_fin] at hh
    rw [Nat.card_eq_fintype_card] at hZ
    omega
  have hside (i : Fin k) : ∃ b : Embedding B.ordered C,
      (z i).val ∈ copyCarrier b ∧ (z (cyclicSucc i)).val ∈ copyCarrier b :=
    contact_comparison_adj_copy hcover (hs i)
  choose b hb using hside
  let s : Finset (Set W) := Finset.univ.image (fun i => copyCarrier (b i))
  have hsi (i : Fin k) : copyCarrier (b i) ∈ s :=
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hsne : s.Nonempty := ⟨copyCarrier (b ⟨0,by omega⟩),hsi _⟩
  have hsc : s.card ≤ n := by
    have hh : s.card ≤ k := by
      simpa [s] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin k)))
        (f := fun i => copyCarrier (b i)))
    exact hh.trans hkn
  have hsrc (S : Set W) (hS : S ∈ s) :
      S ∈ Set.range (ContactActualCarrier.carrier (A := A.ordered) (B := B.ordered) (C := C)) := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hS
    exact ⟨Sum.inl (b i),rfl⟩
  obtain ⟨t,hst,_,_,_,m,hm,hF,_⟩ := hcomp s hsne hsc hsrc
  letI : Nonempty {S // S ∈ t} := by
    obtain ⟨S,hS⟩ := hsne
    exact ⟨⟨S,hst hS⟩⟩
  obtain ⟨J⟩ := hF.joinTree_of_nonempty
  let T : ContactJoinTree (fun i => (m i).carrier) := {
    tree := J.tree
    isTree := J.isTree
    running := by
      intro x
      have he : (fun i : {S // S ∈ t} => (ABMember.supportPiece A.ordered (m i)).carrier) =
          (fun i => (m i).carrier) :=
        funext (fun i => ABMember.supportPiece_carrier A.ordered (m i))
      exact Eq.mp (congrArg (fun f : {S // S ∈ t} → Set W =>
        (J.tree.induce {i | x ∈ f i}).Preconnected) he) (J.running x) }
  have hz : Function.Injective (fun i => (z i).val) :=
    Subtype.val_injective.comp hzi
  have hcycle (i : Fin k) :
      (contactFamilyGraph (fun i => (m i).carrier)).Adj (z i).val (z (cyclicSucc i)).val := by
    refine ⟨(hs i).1,⟨⟨copyCarrier (b i),hst (hsi i)⟩,?_,?_⟩⟩
    · change (z i).val ∈ (m ⟨copyCarrier (b i),hst (hsi i)⟩).carrier
      exact Eq.mpr (congrArg (fun S : Set W => (z i).val ∈ S)
        (hm ⟨copyCarrier (b i),hst (hsi i)⟩)) (hb i).1
    · change (z (cyclicSucc i)).val ∈ (m ⟨copyCarrier (b i),hst (hsi i)⟩).carrier
      exact Eq.mpr (congrArg (fun S : Set W => (z (cyclicSucc i)).val ∈ S)
        (hm ⟨copyCarrier (b i),hst (hsi i)⟩)) (hb i).2
  obtain ⟨i,j,hij,hij',hji',hne,a,hxa,hya⟩ := T.chordal k _ hk hz hcycle
  exact ⟨i,j,hij,hij',hji',contact_mixed_member_clique (m a) _ hxa _ hya hne⟩

/-- The vertices of a positive relation tuple induce an irreducible
substructure, including when the tuple has no entries. -/
theorem contact_relation_range_irreducible
    {R : RelStructure L W} (r : L.Symbol) (x : Fin (L.arity r) → W)
    (hx : R.rel r x) : (R.induce (Set.range x)).Irreducible := by
  intro y z _
  obtain ⟨i,hi⟩ := y.property
  obtain ⟨j,hj⟩ := z.property
  let f (k : Fin (L.arity r)) : Set.range x := ⟨x k,⟨k,rfl⟩⟩
  exact ⟨r,f,i,j,hx,Subtype.ext hi,Subtype.ext hj⟩

/-- A comparison-clique cover of the small vertex set chooses at
most n actual B-copies. Their completed union contains every tuple
of the induced structure, so its supported-tree embedding restricts
to an induced embedding of the entire small structure. -/
theorem contact_small_induced_supported
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V] [Finite W]
    {C : RelStructure L.withOrder W} (g n : ℕ)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    (hcomp : ContactCarrierMixedCompletion A.ordered B.ordered C g n)
    (Z : Set W) (hZ : Nat.card Z ≤ n) :
    ∃ (X : Type v) (T : RelStructure L.withOrder X)
      (e : Embedding (C.induce Z) T),
      ASupportedTreeAmalgam A.ordered B.ordered X T := by
  classical
  letI : Fintype W := Fintype.ofFinite _
  letI : Fintype Z := Fintype.ofFinite _
  by_cases hne : Z.Nonempty
  · letI : Nonempty Z := ⟨⟨hne.choose,hne.choose_spec⟩⟩
    let G := (contactComparisonGraph C).induce Z
    have hG : ContactChordal G := contact_small_comparison_chordal g n hcover hcomp Z hZ
    obtain ⟨s,hs,hsc,hcl,hcov⟩ := contact_chordal_cliqueCover_nonempty G hG
    have hbag (K : {K // K ∈ s}) : ∃ b : Embedding B.ordered C,
        Subtype.val '' K.val ⊆ copyCarrier b := by
      apply hcover
      apply contact_comparison_clique_irreducible
      rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hxy
      exact hcl K.val K.property x hx y hy (fun he => hxy (congrArg Subtype.val he))
    choose b hb using hbag
    let sB : Finset (Set W) := s.attach.image (fun K => copyCarrier (b K))
    have hsB (K : {K // K ∈ s}) : copyCarrier (b K) ∈ sB :=
      Finset.mem_image.mpr ⟨K,Finset.mem_attach _ _,rfl⟩
    have hsBne : sB.Nonempty := by
      obtain ⟨K,hK⟩ := hs
      exact ⟨copyCarrier (b ⟨K,hK⟩),hsB _⟩
    have hsBc : sB.card ≤ n := by
      have hh : sB.card ≤ s.card := by
        simpa [sB] using (Finset.card_image_le (s := s.attach)
          (f := fun K => copyCarrier (b K)))
      rw [Nat.card_eq_fintype_card] at hZ
      omega
    have hsrc (S : Set W) (hS : S ∈ sB) :
        S ∈ Set.range (ContactActualCarrier.carrier (A := A.ordered) (B := B.ordered) (C := C)) := by
      obtain ⟨K,_,rfl⟩ := Finset.mem_image.mp hS
      exact ⟨Sum.inl (b K),rfl⟩
    obtain ⟨t,hst,_,_,_,m,hm,_,X,T,e,hT⟩ := hcomp sB hsBne hsBc hsrc
    let idx (K : {K // K ∈ s}) : {S // S ∈ t} :=
      ⟨copyCarrier (b K),hst (hsB K)⟩
    have hmem (K : {K // K ∈ s}) (z : Z) (hz : z ∈ K.val) :
        z.val ∈ (m (idx K)).carrier := by
      rw [hm]
      exact hb K ⟨z,hz,rfl⟩
    have hvertex (z : Z) : z.val ∈ mixedFamilyCarrier m := by
      have hc : ContactClique G {z} := by
        intro x hx y hy hxy
        exact (hxy ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
      obtain ⟨K,hK,hsub⟩ := hcov {z} hc
      exact Set.mem_iUnion.mpr ⟨idx ⟨K,hK⟩,hmem ⟨K,hK⟩ z (hsub (Set.mem_singleton z))⟩
    have htuple (r : L.withOrder.Symbol) (x : Fin (L.withOrder.arity r) → Z)
        (hx : (C.induce Z).rel r x) :
        ∃ i : {S // S ∈ t}, ∀ k, (x k).val ∈ (m i).carrier := by
      have hc : ContactClique G (Set.range x) := by
        obtain ⟨d,hd⟩ := hcover (Set.range (Subtype.val ∘ x))
          (contact_relation_range_irreducible r (Subtype.val ∘ x) hx)
        rintro y ⟨i,rfl⟩ z ⟨j,rfl⟩ hij
        exact contactComparisonGraph_embedding_ordered d _ (hd ⟨i,rfl⟩)
          _ (hd ⟨j,rfl⟩) (fun he => hij (Subtype.ext he))
      obtain ⟨K,hK,hsub⟩ := hcov (Set.range x) hc
      exact ⟨idx ⟨K,hK⟩,fun k => hmem ⟨K,hK⟩ (x k) (hsub ⟨k,rfl⟩)⟩
    let f : Embedding (C.induce Z) (mixedFamilyUnionStructure C m) := {
      toFun := fun z => ⟨z.val,hvertex z⟩
      injective := fun x y he =>
        Subtype.ext (congrArg (fun z : mixedFamilyCarrier m => z.val) he)
      map_rel_iff := by
        intro r x
        constructor
        · exact fun h => h.1
        · intro hx
          exact ⟨hx,htuple r x hx⟩ }
    exact ⟨X,T,e.comp f,hT⟩
  · have hIrred : (C.induce Z).Irreducible := by
      intro x
      exact (hne ⟨x.val,x.property⟩).elim
    obtain ⟨b,hb⟩ := hcover Z hIrred
    let f := (C.inclusion Z).factorThroughRange b (fun z => by
      obtain ⟨v,hv⟩ := hb z.property
      exact ⟨v,hv.symm⟩)
    exact ⟨V,B.ordered,f,ASupportedTreeAmalgam.copy (Iso.refl _)⟩

end StructuralRamsey.Girth

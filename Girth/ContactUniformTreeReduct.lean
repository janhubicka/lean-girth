import Girth.ContactUniformReduction
import Girth.SupportedTree

/-! Forgetting order preserves the actual free-amalgamation construction.
The final recognition lemma identifies the entire symmetric relation of an
unordered hypergraph, including relation reflection on induced substructures. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W X : Type v}

def contactOrderReduct_embedding
    {A : RelStructure L.withOrder U} {B : RelStructure L.withOrder V}
    (f : Embedding A B) : Embedding A.orderReduct B.orderReduct where
  toFun := f
  injective := f.injective
  map_rel_iff := fun R x => f.map_rel_iff (.inl R) x

def contactOrderReduct_iso
    {A : RelStructure L.withOrder U} {B : RelStructure L.withOrder V}
    (f : Iso A B) : Iso A.orderReduct B.orderReduct where
  toEquiv := f.toEquiv
  map_rel_iff := fun R x => f.map_rel_iff (.inl R) x

theorem contactOrderReduct_free
    {D : RelStructure L.withOrder U} {A : RelStructure L.withOrder V}
    {B : RelStructure L.withOrder W} {C : RelStructure L.withOrder X}
    {fA : Embedding D A} {fB : Embedding D B}
    {iA : Embedding A C} {iB : Embedding B C}
    (h : IsFreeAmalgam fA fB iA iB) :
    IsFreeAmalgam (contactOrderReduct_embedding fA) (contactOrderReduct_embedding fB)
      (contactOrderReduct_embedding iA) (contactOrderReduct_embedding iB) where
  covers := h.covers
  overlap := h.overlap
  rel_iff := fun R x => h.rel_iff (.inl R) x

/-- An ordered supported tree becomes a supported tree of the
non-order structures, with exactly the same identifications. -/
theorem ASupportedTreeAmalgam.contact_orderReduct
    {A : RelStructure L.withOrder U} {B : RelStructure L.withOrder V}
    {T : RelStructure L.withOrder W}
    (h : ASupportedTreeAmalgam A B W T) :
    ASupportedTreeAmalgam A.orderReduct B.orderReduct W T.orderReduct := by
  induction h with
  | copy f => exact .copy (contactOrderReduct_iso f)
  | glueA h f₀ fB i₀ iB hfree ih =>
    exact .glueA ih (contactOrderReduct_embedding f₀) (contactOrderReduct_embedding fB)
      (contactOrderReduct_embedding i₀) (contactOrderReduct_embedding iB)
      (contactOrderReduct_free hfree)
  | gluePoint h f₀ fB hs₀ hsB i₀ iB hfree ih =>
    obtain ⟨a₀,ha₀⟩ := hs₀
    obtain ⟨aB,haB⟩ := hsB
    exact .gluePoint ih (contactOrderReduct_embedding f₀) (contactOrderReduct_embedding fB)
      ⟨contactOrderReduct_embedding a₀,ha₀⟩ ⟨contactOrderReduct_embedding aB,haB⟩
      (contactOrderReduct_embedding i₀) (contactOrderReduct_embedding iB)
      (contactOrderReduct_free hfree)

/-- No tuple information is lost when the covered relational union
is read as a symmetric uniform hypergraph. -/
theorem contact_uniform_tuple_rel_iff [Fintype U] [Finite V]
    [LinearOrder U] [LinearOrder V] {a : ℕ} (ha : Fintype.card U = a)
    (F : Set (Set V)) (hu : ∀ e ∈ F, Nat.card e = a)
    (C : RelStructure (contactUniformLanguage a).withOrder W)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding (contactUniformStructure a F).ordered C, S ⊆ copyCarrier b)
    (x : Fin a → W) :
    C.rel (.inl ()) x ↔
      Function.Injective x ∧ Set.range x ∈ contactUniformReduct a C := by
  classical
  constructor
  · intro hx
    obtain ⟨b,hb⟩ := hcover (Set.range x) (contact_uniform_tuple_irreducible x hx)
    have hex (i : Fin a) : ∃ y : V, b y = x i := hb ⟨i,rfl⟩
    choose y hy using hex
    have he : b.toFun ∘ y = x := funext hy
    have hrel : (contactUniformStructure a F).ordered.rel (.inl ()) y :=
      (b.map_rel_iff (.inl ()) y).mp (he.symm ▸ hx)
    have hi : Function.Injective x := he ▸ b.injective.comp hrel.1
    exact ⟨hi,x,hi,hx,rfl⟩
  · rintro ⟨hi,hx⟩
    have hs := contact_uniform_support_reduct ha F hu C hcover
    have hx' : Set.range x ∈ supportCopies (contactUniformEdge a U).ordered C :=
      hs.symm ▸ hx
    obtain ⟨b,hb⟩ := hx'
    have hex (i : Fin a) : ∃ y : U, b y = x i := by
      have hm : x i ∈ copyCarrier b := hb ▸ (show x i ∈ Set.range x from ⟨i,rfl⟩)
      exact hm
    choose y hy using hex
    have he : b.toFun ∘ y = x := funext hy
    have hyi : Function.Injective y := by
      intro i j hij
      apply hi
      exact (hy i).symm.trans ((congrArg b hij).trans (hy j))
    have hrel : (contactUniformEdge a U).ordered.rel (.inl ()) y :=
      ⟨hyi,Set.mem_singleton_iff.mpr (Set.range_eq_univ.mpr
        (contact_uniform_tuple_surjective ha y hyi))⟩
    exact he ▸ (b.map_rel_iff (.inl ()) y).mpr hrel

/-- Identity on the vertex set identifies the full induced
hypergraph with the non-order part of the relational witness. -/
def contact_uniform_induced_reduct [Fintype U] [Finite V]
    [LinearOrder U] [LinearOrder V] {a : ℕ} (ha : Fintype.card U = a)
    (F : Set (Set V)) (hu : ∀ e ∈ F, Nat.card e = a)
    (C : RelStructure (contactUniformLanguage a).withOrder W)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding (contactUniformStructure a F).ordered C, S ⊆ copyCarrier b)
    (Z : Set W) :
    Embedding ((contactUniformStructure a (contactUniformReduct a C)).induce Z)
      (C.induce Z).orderReduct where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := by
    intro R x
    cases R
    exact contact_uniform_tuple_rel_iff ha F hu C hcover (Subtype.val ∘ x)

end StructuralRamsey.Girth

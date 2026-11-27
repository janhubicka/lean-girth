import Girth.ContactRelationalUnion
import Mathlib.Data.Finset.Sort

/-! Symmetric uniform hypergraphs as one-relation structures.
An edge is represented by every injective enumeration of its carrier.
The ambient order need only be an acyclic subrelation of a linear order:
covering irreducibles by original B-copies is what gives an ordered
A-embedding on every edge of the unordered reduct. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe v
variable {U V W : Type v}

def contactUniformLanguage (a : ℕ) : RelLanguage.{0} where
  Symbol := Unit
  arity := fun _ => a

def contactUniformStructure (a : ℕ) (H : Set (Set V)) :
    RelStructure (contactUniformLanguage a) V where
  rel _ x := Function.Injective x ∧ Set.range x ∈ H

def contactUniformEdge (a : ℕ) (U : Type v) :
    RelStructure (contactUniformLanguage a) U :=
  contactUniformStructure a {Set.univ}

def contactUniformReduct (a : ℕ)
    (C : RelStructure (contactUniformLanguage a).withOrder W) : Set (Set W) :=
  {S | ∃ x : Fin a → W, Function.Injective x ∧ C.rel (.inl ()) x ∧ Set.range x = S}

theorem contact_uniform_range_comp {X : Type*} (f : V → W) (x : X → V) :
    Set.range (f ∘ x) = f '' Set.range x := by
  ext z
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨x i,⟨i,rfl⟩,rfl⟩
  · rintro ⟨y,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩

theorem contact_uniform_tuple_surjective [Fintype U] {a : ℕ}
    (ha : Fintype.card U = a) (x : Fin a → U) (hx : Function.Injective x) :
    Function.Surjective x := by
  classical
  by_contra hn
  have h := Fintype.card_lt_of_injective_not_surjective x hx hn
  rw [Fintype.card_fin,ha] at h
  exact (Nat.lt_irrefl a h)

/-- Every finite set of the right size admits an increasing
enumeration from the ordered edge template. -/
theorem contact_uniform_placement [Fintype U] [Finite V]
    [LinearOrder U] [LinearOrder V] {a : ℕ} (ha : Fintype.card U = a)
    (S : Set V) (hS : Nat.card S = a) :
    ∃ f : U ↪o V, Set.range f = S := by
  classical
  letI : Fintype S := Fintype.ofFinite _
  have hc : Fintype.card S = a := by
    rw [← Nat.card_eq_fintype_card]
    exact hS
  let e : U ≃o S := (Fintype.orderIsoFinOfCardEq U ha).symm.trans
    (Fintype.orderIsoFinOfCardEq S hc)
  let f : U ↪o V := e.toOrderEmbedding.trans (OrderEmbedding.subtype S)
  refine ⟨f,?_⟩
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    exact (e u).property
  · intro hx
    exact ⟨e.symm ⟨x,hx⟩,congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)⟩

/-- An increasing map onto a hyperedge is an induced embedding of
the ordered one-edge structure, not just a positive homomorphism. -/
def contact_uniform_edge_embedding [Fintype U] [LinearOrder U] [LinearOrder V]
    {a : ℕ} (ha : Fintype.card U = a) {H : Set (Set V)}
    (f : U ↪o V) (hf : Set.range f ∈ H) :
    Embedding (contactUniformEdge a U).ordered (contactUniformStructure a H).ordered where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl r =>
      change (Function.Injective (f ∘ x) ∧ Set.range (f ∘ x) ∈ H) ↔
        (Function.Injective x ∧ Set.range x ∈ ({Set.univ} : Set (Set U)))
      constructor
      · intro h
        have hi : Function.Injective x := fun i j he => h.1 (congrArg f he)
        exact ⟨hi,Set.mem_singleton_iff.mpr (Set.range_eq_univ.mpr
          (contact_uniform_tuple_surjective ha x hi))⟩
      · intro h
        refine ⟨f.injective.comp h.1,?_⟩
        rw [contact_uniform_range_comp,Set.mem_singleton_iff.mp h.2,Set.image_univ]
        exact hf
    | inr r =>
      change f (x (0 : Fin 2)) < f (x (1 : Fin 2)) ↔
        x (0 : Fin 2) < x (1 : Fin 2)
      exact f.strictMono.lt_iff_lt

theorem contact_uniform_copy_edge [Fintype U] [LinearOrder U]
    {a : ℕ} (ha : Fintype.card U = a)
    {C : RelStructure (contactUniformLanguage a).withOrder W}
    (f : Embedding (contactUniformEdge a U).ordered C) :
    copyCarrier f ∈ contactUniformReduct a C := by
  let k := Fintype.orderIsoFinOfCardEq U ha
  have h : (contactUniformEdge a U).ordered.rel (.inl ()) k :=
    ⟨k.injective,Set.mem_singleton_iff.mpr (Set.range_eq_univ.mpr k.surjective)⟩
  refine ⟨f ∘ k,f.injective.comp k.injective,(f.map_rel_iff (.inl ()) k).mpr h,?_⟩
  change Set.range (f.toFun ∘ k) = Set.range f
  rw [contact_uniform_range_comp,Set.range_eq_univ.mpr k.surjective,Set.image_univ]

theorem contact_uniform_reduct_ordered [Finite V] [LinearOrder V]
    {a : ℕ} (H : Set (Set V)) (hu : ∀ S ∈ H, Nat.card S = a) :
    contactUniformReduct a (contactUniformStructure a H).ordered = H := by
  classical
  ext S
  constructor
  · rintro ⟨x,_,h,rfl⟩
    exact h.2
  · intro hS
    letI : Fintype S := Fintype.ofFinite _
    have hc : Fintype.card S = a := by
      rw [← Nat.card_eq_fintype_card]
      exact hu S hS
    let k := Fintype.orderIsoFinOfCardEq S hc
    let x (i : Fin a) : V := (k i).val
    have hi : Function.Injective x := fun i j h => k.injective (Subtype.ext h)
    have he : Set.range x = S := by
      ext z
      constructor
      · rintro ⟨i,rfl⟩
        exact (k i).property
      · intro hz
        exact ⟨k.symm ⟨z,hz⟩,congrArg Subtype.val (k.apply_symm_apply ⟨z,hz⟩)⟩
    exact ⟨x,hi,⟨hi,he.symm ▸ hS⟩,he⟩

theorem contact_uniform_support_ordered [Fintype U] [Finite V]
    [LinearOrder U] [LinearOrder V] {a : ℕ} (ha : Fintype.card U = a)
    (H : Set (Set V)) (hu : ∀ S ∈ H, Nat.card S = a) :
    supportCopies (contactUniformEdge a U).ordered (contactUniformStructure a H).ordered = H := by
  ext S
  constructor
  · rintro ⟨f,rfl⟩
    have h := contact_uniform_copy_edge ha f
    rw [contact_uniform_reduct_ordered H hu] at h
    exact h
  · intro hS
    obtain ⟨f,hf⟩ := contact_uniform_placement (U := U) ha S (hu S hS)
    let e := contact_uniform_edge_embedding ha f (hf.symm ▸ hS)
    exact ⟨e,hf.symm⟩

/-- A positive hyperedge tuple is an irreducible induced carrier,
whether or not the ambient order is already total. -/
theorem contact_uniform_tuple_irreducible {a : ℕ}
    {C : RelStructure (contactUniformLanguage a).withOrder W}
    (x : Fin a → W) (hx : C.rel (.inl ()) x) :
    (C.induce (Set.range x)).Irreducible := by
  intro u v _
  obtain ⟨i,hi⟩ := u.property
  obtain ⟨j,hj⟩ := v.property
  let y (k : Fin a) : Set.range x := ⟨x k,⟨k,rfl⟩⟩
  exact ⟨.inl (),y,i,j,hx,Subtype.ext hi,Subtype.ext hj⟩

/-- In a relational witness every unordered hyperedge is exactly
one ordered A-copy. This is the nontrivial direction in forgetting
the ambient order. -/
theorem contact_uniform_support_reduct [Fintype U] [Finite V]
    [LinearOrder U] [LinearOrder V] {a : ℕ} (ha : Fintype.card U = a)
    (H : Set (Set V)) (hu : ∀ S ∈ H, Nat.card S = a)
    (C : RelStructure (contactUniformLanguage a).withOrder W)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding (contactUniformStructure a H).ordered C, S ⊆ copyCarrier b) :
    supportCopies (contactUniformEdge a U).ordered C = contactUniformReduct a C := by
  classical
  ext S
  constructor
  · rintro ⟨f,rfl⟩
    exact contact_uniform_copy_edge ha f
  · rintro ⟨x,hxi,hx,rfl⟩
    obtain ⟨b,hb⟩ := hcover (Set.range x) (contact_uniform_tuple_irreducible x hx)
    have hex (i : Fin a) : ∃ y : V, b y = x i := hb ⟨i,rfl⟩
    choose y hy using hex
    have hEq : b.toFun ∘ y = x := funext hy
    have hyrel : (contactUniformStructure a H).ordered.rel (.inl ()) y := by
      apply (b.map_rel_iff (.inl ()) y).mp
      exact hEq.symm ▸ hx
    have hY : Set.range y ∈ H := hyrel.2
    have hS : Set.range y ∈ supportCopies (contactUniformEdge a U).ordered
        (contactUniformStructure a H).ordered := by
      rw [contact_uniform_support_ordered ha H hu]
      exact hY
    obtain ⟨f,hf⟩ := hS
    refine ⟨b.comp f,?_⟩
    change Set.range x = Set.range (b.toFun ∘ f.toFun)
    calc
      Set.range x = b.toFun '' Set.range y := by rw [← hEq,contact_uniform_range_comp]
      _ = b.toFun '' Set.range f := congrArg (fun S : Set V => b.toFun '' S) hf
      _ = Set.range (b.toFun ∘ f.toFun) := (contact_uniform_range_comp _ _).symm

/-- A positive hypergraph relation remains symmetric on the
unordered reduct of an actual ordered B-embedding. Every edge
contained in its image is reflected to a source edge. -/
theorem contact_uniform_copy_induced [Finite V] {a : ℕ}
    (H : Set (Set V)) (hu : ∀ S ∈ H, Nat.card S = a)
    [LinearOrder V]
    {C : RelStructure (contactUniformLanguage a).withOrder W}
    (b : Embedding (contactUniformStructure a H).ordered C) (S : Set V) :
    S ∈ H ↔ b.toFun '' S ∈ contactUniformReduct a C := by
  classical
  constructor
  · intro hs
    have ht : S ∈ contactUniformReduct a (contactUniformStructure a H).ordered := by
      rw [contact_uniform_reduct_ordered H hu]
      exact hs
    obtain ⟨x,hi,hx,he⟩ := ht
    refine ⟨b ∘ x,b.injective.comp hi,(b.map_rel_iff (.inl ()) x).mpr hx,?_⟩
    rw [contact_uniform_range_comp,he]
  · rintro ⟨x,hi,hx,he⟩
    have hex (i : Fin a) : ∃ y : V, y ∈ S ∧ b y = x i := by
      have h : x i ∈ b.toFun '' S := he ▸ (show x i ∈ Set.range x from ⟨i,rfl⟩)
      exact h
    choose y hy using hex
    have hEq : b.toFun ∘ y = x := funext (fun i => (hy i).2)
    have hrel : (contactUniformStructure a H).ordered.rel (.inl ()) y := by
      apply (b.map_rel_iff (.inl ()) y).mp
      exact hEq.symm ▸ hx
    have hr : Set.range y = S := by
      ext z
      constructor
      · rintro ⟨i,rfl⟩
        exact (hy i).1
      · intro hz
        have h : b z ∈ Set.range x := he.symm ▸ (show b z ∈ b.toFun '' S from ⟨z,hz,rfl⟩)
        obtain ⟨i,hi⟩ := h
        exact ⟨i,b.injective ((hy i).2.trans hi)⟩
    have hY : Set.range y ∈ H := hrel.2
    exact hr ▸ hY

end StructuralRamsey.Girth

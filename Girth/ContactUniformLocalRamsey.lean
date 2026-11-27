import Girth.ContactUniformReduction
import Girth.ContactCarrierCompletion

/-! The unordered hypergraph theorem is a consequence of the
literal relational set-family theorem. All of the hypergraph
objects here are sets of vertex sets; there is no duplicate edge
label or duplicate designated image in the completion count. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe v
variable {U V W : Type v}

/-- The hypergraph induced on one carrier, with its full support. -/
def contactInducedHypergraphPiece (H : Set (Set W)) (S : Set W) :
    HypergraphPiece W where
  carrier := S
  edges := {e | e ∈ H ∧ e ⊆ S}
  edge_subset_carrier := fun {_} he => he.2

theorem contact_uniform_supportPiece
    {L : RelLanguage} {A : RelStructure L U} {B : RelStructure L V}
    {C : RelStructure L W} [Finite U] (m : ABMember A B C) :
    m.supportPiece A = contactInducedHypergraphPiece (supportCopies A C) m.carrier := by
  have he : (m.supportPiece A).edges =
      (contactInducedHypergraphPiece (supportCopies A C) m.carrier).edges := by
    cases m with
    | a a =>
      ext e
      change e ∈ ({copyCarrier a} : Set (Set W)) ↔
        e ∈ supportCopies A C ∧ e ⊆ copyCarrier a
      constructor
      · intro h
        have hh := Set.mem_singleton_iff.mp h
        subst e
        exact ⟨⟨a,rfl⟩,Set.Subset.rfl⟩
      · rintro ⟨⟨b,hb⟩,hsub⟩
        apply Set.mem_singleton_iff.mpr
        have h : SameCopy b a := sameCopy_of_range_subset b a (by
          intro x
          have hx : b x ∈ copyCarrier a := hsub (hb.symm ▸ (show b x ∈ copyCarrier b from ⟨x,rfl⟩))
          obtain ⟨y,hy⟩ := hx
          exact ⟨y,hy.symm⟩)
        exact hb.trans h
    | b b =>
      ext e
      change (∃ a : Embedding A C, copyCarrier a = e ∧ copyCarrier a ⊆ copyCarrier b) ↔
        e ∈ supportCopies A C ∧ e ⊆ copyCarrier b
      constructor
      · rintro ⟨a,ha,hs⟩
        exact ⟨⟨a,ha.symm⟩,ha ▸ hs⟩
      · rintro ⟨⟨a,ha⟩,hs⟩
        exact ⟨a,ha.symm,ha ▸ hs⟩
  have hc : (m.supportPiece A).carrier =
      (contactInducedHypergraphPiece (supportCopies A C) m.carrier).carrier :=
    ABMember.supportPiece_carrier A m
  generalize hp : m.supportPiece A = p at hc he ⊢
  generalize hq : contactInducedHypergraphPiece (supportCopies A C) m.carrier = q at hc he ⊢
  cases p
  cases q
  cases hc
  cases he
  rfl

open Classical in
def ContactUniformLocalCompletion (H D : Set (Set W)) (g n : ℕ) : Prop :=
  ∀ s : Finset (Set W), s.Nonempty → s.card ≤ n →
    (∀ S ∈ s, S ∈ D ∪ H) →
    ∃ t : Finset (Set W), s ⊆ t ∧
      (∀ S ∈ t, S ∉ s → S ∈ D) ∧
      (s.card = 1 → t = s) ∧
      (g-1)*(t \ s).card ≤ s.card-2 ∧
      ForestOfCopies (fun S : {S // S ∈ t} => contactInducedHypergraphPiece H S.val)

/-- A relational completion gives exactly the hypergraph pieces
and cardinality bound after forgetting the language. -/
theorem contact_uniform_completion_transfer
    {L : RelLanguage} {A : RelStructure L U} {B : RelStructure L V}
    {C : RelStructure L W} [Finite U] (g n : ℕ)
    (h : ContactCarrierMixedCompletion A B C g n) :
    ContactUniformLocalCompletion (supportCopies A C) (supportCopies B C) g n := by
  classical
  intro s hs hc hsrc
  have hsrc' (S : Set W) (hS : S ∈ s) : S ∈ Set.range
      (ContactActualCarrier.carrier (A := A) (B := B) (C := C)) := by
    rcases hsrc S hS with h | h
    · obtain ⟨b,hb⟩ := h
      exact ⟨Sum.inl b,hb.symm⟩
    · obtain ⟨a,ha⟩ := h
      exact ⟨Sum.inr a,ha.symm⟩
  obtain ⟨t,hst,hadd,h1,hcost,m,hm,hF,_⟩ := h s hs hc hsrc'
  refine ⟨t,hst,?_,h1,hcost,?_⟩
  · intro S hS hn
    obtain ⟨b,hb⟩ := hadd S hS hn
    exact ⟨b,hb.symm⟩
  have he : (fun i : {S // S ∈ t} => (m i).supportPiece A) =
      (fun i : {S // S ∈ t} => contactInducedHypergraphPiece (supportCopies A C) i.val) := by
    funext i
    rw [contact_uniform_supportPiece,hm i]
  exact he ▸ hF

/-- Explicit unordered witness statement. Its designated copies
are identified by their induced carrier sets; the colouring
ranges over ALL ambient edges. -/
def ContactUniformRamseyWitness (a : ℕ) (F : Set (Set V))
    (g n : ℕ) (Color : Type v) : Prop :=
  ∃ (W : Type v) (H D : Set (Set W)),
    Finite W ∧ (∀ e ∈ H, Nat.card e = a) ∧
    GirthGT H g ∧
    (∀ S ∈ D, ∃ f : V ↪ W, Set.range f = S ∧
      ∀ e : Set V, e ∈ F ↔ f '' e ∈ H) ∧
    (∀ S ∈ D, ∀ e ∈ H, ¬ (e ∩ S).Subsingleton → e ⊆ S) ∧
    (∀ x : W, ∃ S ∈ D, x ∈ S) ∧
    (∀ e ∈ H, ∃ S ∈ D, e ⊆ S) ∧
    (∀ χ : H → Color, ∃ S ∈ D, ∃ c : Color,
      ∀ e : H, e.val ⊆ S → χ e = c) ∧
    ContactUniformLocalCompletion H D g n

theorem contactUniformLocalRamsey_of_relational
    [Fintype U] [LinearOrder U] [Finite V] [LinearOrder V]
    {a : ℕ} (ha : Fintype.card U = a) (ha₂ : 2 ≤ a)
    (F : Set (Set V)) (hu : ∀ e ∈ F, Nat.card e = a) (hne : F.Nonempty)
    (g n : ℕ) (hg : 2 ≤ g) (hn : 2 ≤ n) (hG : GirthGT F g)
    (Color : Type v) [Finite Color] [Nonempty Color] :
    ContactUniformRamseyWitness a F g n Color := by
  classical
  let A := contactUniformEdge a U
  let B := contactUniformStructure a F
  have hSource : supportCopies A.ordered B.ordered = F :=
    contact_uniform_support_ordered ha F hu
  obtain ⟨e,he⟩ := hne
  have he' : e ∈ supportCopies A.ordered B.ordered := hSource.symm ▸ he
  obtain ⟨α,_⟩ := he'
  obtain ⟨W,C,o,hfin,hord,harr,hcover,hcomp,hgirth,hstrong,_,_⟩ :=
    contactRelationalGirthRamsey_carriers A B (ha.symm ▸ ha₂) α g n hg hn
      (hSource.symm ▸ hG) Color
  letI : LinearOrder W := o
  letI : Finite W := hfin
  let H := contactUniformReduct a C
  let D := supportCopies B.ordered C
  have hH : supportCopies A.ordered C = H :=
    contact_uniform_support_reduct ha F hu C hcover
  refine ⟨W,H,D,hfin,?_,hH ▸ hgirth,?_,?_,?_,?_,?_,?_⟩
  · intro e he
    obtain ⟨x,hxi,_,hx⟩ := he
    let f (i : Fin a) : e := ⟨x i,hx ▸ (show x i ∈ Set.range x from ⟨i,rfl⟩)⟩
    have hfi : Function.Injective f := fun i j h => hxi (congrArg Subtype.val h)
    have hfs : Function.Surjective f := by
      intro z
      have hz : z.val ∈ Set.range x := hx.symm ▸ z.property
      obtain ⟨i,hi⟩ := hz
      exact ⟨i,Subtype.ext hi⟩
    let e' := Equiv.ofBijective f ⟨hfi,hfs⟩
    exact (Nat.card_congr e'.symm).trans (by simp)
  · intro S hS
    obtain ⟨b,hb⟩ := hS
    exact ⟨b.toFunctionEmbedding,hb.symm,contact_uniform_copy_induced F hu b⟩
  · intro S hS e he hn
    obtain ⟨b,hb⟩ := hS
    have he' : e ∈ supportCopies A.ordered C := hH.symm ▸ he
    obtain ⟨a,ha'⟩ := he'
    rw [hb,ha'] at hn ⊢
    exact hstrong b a hn
  · intro x
    have hi : (C.induce ({x} : Set W)).Irreducible := by
      intro y z hn
      exact (hn (Subtype.ext ((Set.mem_singleton_iff.mp y.property).trans
        (Set.mem_singleton_iff.mp z.property).symm))).elim
    obtain ⟨b,hb⟩ := hcover {x} hi
    exact ⟨copyCarrier b,⟨b,rfl⟩,hb (Set.mem_singleton x)⟩
  · intro e he
    have he' : e ∈ supportCopies A.ordered C := hH.symm ▸ he
    obtain ⟨a,ha'⟩ := he'
    obtain ⟨b,hb⟩ := hcover (copyCarrier a) ((contact_ordered_irreducible A).range_embedding a)
    exact ⟨copyCarrier b,⟨b,rfl⟩,ha'.symm ▸ hb⟩
  · intro χ
    let ψ (a : Embedding A.ordered C) : Color := χ ⟨copyCarrier a,
      hH ▸ (show copyCarrier a ∈ supportCopies A.ordered C from ⟨a,rfl⟩)⟩
    obtain ⟨b,hb⟩ := harr ψ
    refine ⟨copyCarrier b,⟨b,rfl⟩,ψ (b.comp α),?_⟩
    intro e he
    have he' : e.val ∈ supportCopies A.ordered C := hH.symm ▸ e.property
    obtain ⟨a,ha'⟩ := he'
    have hex (x : U) : ∃ y : V, a x = b y := by
      obtain ⟨y,hy⟩ := he (ha'.symm ▸ (show a x ∈ copyCarrier a from ⟨x,rfl⟩))
      exact ⟨y,hy.symm⟩
    let d := a.factorThroughRange b hex
    have hEq : b.comp d = a := Embedding.ext (fun x => (Classical.choose_spec (hex x)).symm)
    have hmono := hb d α
    change ψ (b.comp d) = ψ (b.comp α) at hmono
    rw [hEq] at hmono
    have hχ : e = (⟨copyCarrier a,hH ▸ (show copyCarrier a ∈ supportCopies A.ordered C from ⟨a,rfl⟩)⟩ : H) :=
      Subtype.ext ha'
    rw [hχ]
    exact hmono
  · have h := contact_uniform_completion_transfer g n hcomp
    rw [hH] at h
    exact h

/-- Unordered hypergraph form, with no order supplied on the input. -/
theorem contactUniformLocalRamsey [Finite V] (a : ℕ) (ha : 2 ≤ a)
    (F : Set (Set V)) (hu : ∀ e ∈ F, Nat.card e = a) (hne : F.Nonempty)
    (g n : ℕ) (hg : 2 ≤ g) (hn : 2 ≤ n) (hG : GirthGT F g)
    (Color : Type v) [Finite Color] [Nonempty Color] :
    ContactUniformRamseyWitness a F g n Color := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  let ev := Fintype.equivFin V
  letI : LinearOrder V := LinearOrder.lift' ev ev.injective
  let U := ULift.{v} (Fin a)
  letI : Fintype U := inferInstanceAs (Fintype (ULift.{v} (Fin a)))
  letI : LinearOrder U := LinearOrder.lift' (fun x : U => x.down)
    (fun x y h => ULift.ext h)
  have hcard : Fintype.card U = a := by simp [U]
  exact contactUniformLocalRamsey_of_relational hcard ha F hu hne g n hg hn hG Color

end StructuralRamsey.Girth

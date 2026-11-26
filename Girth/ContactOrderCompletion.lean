import Girth.ContactOrderReduct
import Girth.ContactCarrierCompletion

/-! Order completion preserves the precise generated mixed union,
not the induced structure on the union of its vertices. This is the
remaining completion clause of the ordered corollary. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W I : Type v}
variable {A : RelStructure L U} {B : RelStructure L V}
variable [LinearOrder U] [LinearOrder V] [LinearOrder W]
variable {C : RelStructure L.withOrder W}

/-- Complete the order on the ambient structure, retaining the same
source, carrier and embedding map of every selected member. -/
def contactCompleteOrder_member (hC : C.ExtendsOrder) :
    ABMember A.ordered B.ordered C →
    ABMember A.ordered B.ordered C.completeOrder
  | .a a => .a (a.completeOrder hC)
  | .b b => .b (b.completeOrder hC)

theorem contactCompleteOrder_member_carrier (hC : C.ExtendsOrder)
    (m : ABMember A.ordered B.ordered C) :
    (contactCompleteOrder_member hC m).carrier = m.carrier := by
  cases m <;> rfl

theorem contactCompleteOrder_member_rel_iff
    (hC : C.ExtendsOrder) (m : ABMember A.ordered B.ordered C)
    (R : L.withOrder.Symbol) (x : Fin (L.withOrder.arity R) → W)
    (hx : ∀ i, x i ∈ m.carrier) :
    C.completeOrder.rel R x ↔ C.rel R x := by
  cases m with
  | a a => exact contactCompleteOrder_rel_iff_on_copy hC a R x hx
  | b b => exact contactCompleteOrder_rel_iff_on_copy hC b R x hx

/-- Extensionality without dependence on the proof that edges
are contained in the carrier. -/
theorem contactHypergraphPiece_eq {p q : HypergraphPiece W}
    (hc : p.carrier = q.carrier) (he : p.edges = q.edges) :
    p = q := by
  cases p
  cases q
  cases hc
  cases he
  rfl

theorem contactCompleteOrder_member_piece
    (hC : C.ExtendsOrder)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    (hA : A.Irreducible) (m : ABMember A.ordered B.ordered C) :
    ((contactCompleteOrder_member hC m).supportPiece A.ordered) =
      m.supportPiece A.ordered := by
  cases m with
  | a a => rfl
  | b b =>
    apply contactHypergraphPiece_eq
    · rfl
    · ext e
      change (∃ a : Embedding A.ordered C.completeOrder,
        copyCarrier a = e ∧ copyCarrier a ⊆ copyCarrier (b.completeOrder hC)) ↔
        (∃ a : Embedding A.ordered C,
          copyCarrier a = e ∧ copyCarrier a ⊆ copyCarrier b)
      constructor
      · rintro ⟨a,ha,hsub⟩
        exact ⟨contactCompleteOrder_lift hC hcover hA a,ha,hsub⟩
      · rintro ⟨a,ha,hsub⟩
        exact ⟨a.completeOrder hC,ha,hsub⟩

/-- The identity on the underlying union is an induced embedding
of the completed generated union back into the original generated
union. It is not asserted for arbitrary ambient induced unions. -/
def contactCompleteOrder_mixedUnion
    (hC : C.ExtendsOrder) (m : I → ABMember A.ordered B.ordered C) :
    Embedding (mixedFamilyUnionStructure C.completeOrder
        (fun i => contactCompleteOrder_member hC (m i)))
      (mixedFamilyUnionStructure C m) where
  toFun x := ⟨x.val,by
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp x.property
    exact Set.mem_iUnion.mpr ⟨i,contactCompleteOrder_member_carrier hC (m i) ▸ hi⟩⟩
  injective := fun _ _ h => Subtype.ext (congrArg Subtype.val h)
  map_rel_iff := by
    intro R x
    change (C.rel R (Subtype.val ∘ x) ∧
      ∃ i, ∀ k, (x k).val ∈ (m i).carrier) ↔
      (C.completeOrder.rel R (Subtype.val ∘ x) ∧
      ∃ i, ∀ k, (x k).val ∈ (contactCompleteOrder_member hC (m i)).carrier)
    constructor
    · rintro ⟨hx,i,hi⟩
      have he := contactCompleteOrder_member_carrier hC (m i)
      exact ⟨(contactCompleteOrder_member_rel_iff hC (m i) R _ hi).mpr hx,
        i,fun k => he.symm ▸ hi k⟩
    · rintro ⟨hx,i,hi⟩
      have he := contactCompleteOrder_member_carrier hC (m i)
      have hi' : ∀ k, (x k).val ∈ (m i).carrier := fun k => he ▸ hi k
      exact ⟨(contactCompleteOrder_member_rel_iff hC (m i) R _ hi').mp hx,i,hi'⟩

/-- The exact same selected and auxiliary carrier families witness
the local-tree completion after order extension. All costs are
literally unchanged, including the singleton case. -/
theorem contactCompleteOrder_carrierCompletion
    (hC : C.ExtendsOrder)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    (hA : A.Irreducible) (hB : B.Irreducible)
    (g n : ℕ) (h : ContactCarrierMixedCompletion A.ordered B.ordered C g n) :
    ContactCarrierMixedCompletion A.ordered B.ordered C.completeOrder g n := by
  classical
  intro s hs hn hsrc
  have hsrc' (X : Set W) (hX : X ∈ s) : X ∈ Set.range
      (ContactActualCarrier.carrier (A := A.ordered) (B := B.ordered) (C := C)) := by
    obtain ⟨a,ha⟩ := hsrc X hX
    cases a with
    | inl b => exact ⟨Sum.inl (contactCompleteOrder_lift hC hcover hB b),ha⟩
    | inr a => exact ⟨Sum.inr (contactCompleteOrder_lift hC hcover hA a),ha⟩
  obtain ⟨t,hst,hadd,hsingle,hcost,m,hm,hforest,Y,D,e,hD⟩ :=
    h s hs hn hsrc'
  let m' (X : {X // X ∈ t}) := contactCompleteOrder_member hC (m X)
  have he : (fun X => (m' X).supportPiece A.ordered) =
      (fun X => (m X).supportPiece A.ordered) :=
    funext (fun X => contactCompleteOrder_member_piece hC hcover hA (m X))
  refine ⟨t,hst,?_,hsingle,hcost,m',?_,?_,Y,D,
    e.comp (contactCompleteOrder_mixedUnion hC m),hD⟩
  · intro X hX hn
    obtain ⟨b,hb⟩ := hadd X hX hn
    exact ⟨b.completeOrder hC,hb⟩
  · intro X
    exact (contactCompleteOrder_member_carrier hC (m X)).trans (hm X)
  · rw [he]
    exact hforest

/-- All of (i), (iv), (v) of the circulation theorem for the
completed linear order, assuming both reducts irreducible.
The irreducible-cover clause (iii) is not asserted for the
completed order, which could make the entire carrier irreducible. -/
theorem contactCompleteOrder_fullCorollary
    (hC : C.ExtendsOrder)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    (hA : A.Irreducible) (hB : B.Irreducible)
    (g n : ℕ) (Color : Type v)
    (hArrow : StructuralRamsey.Arrow A.ordered B.ordered C Color)
    (hG : GirthGT (supportCopies A.ordered C) g)
    (hcomp : ContactCarrierMixedCompletion A.ordered B.ordered C g n)
    (hStrong : ∀ b : Embedding B.ordered C, AStrong A.ordered C (copyCarrier b))
    (hInter : BIntersectionsControlled A.ordered B.ordered C)
    (hShared : BSingletonIntersectionsSupported A.ordered B.ordered C) :
    StructuralRamsey.Arrow A.ordered B.ordered C.completeOrder Color ∧
      GirthGT (supportCopies A.ordered C.completeOrder) g ∧
      ContactCarrierMixedCompletion A.ordered B.ordered C.completeOrder g n ∧
      (∀ b : Embedding B.ordered C.completeOrder, AStrong A.ordered C.completeOrder (copyCarrier b)) ∧
      BIntersectionsControlled A.ordered B.ordered C.completeOrder ∧
      BSingletonIntersectionsSupported A.ordered B.ordered C.completeOrder := by
  obtain ⟨hg,ha⟩ := contactCompleteOrder_girth_arrow hC hcover hA g Color hG hArrow
  exact ⟨ha,hg,contactCompleteOrder_carrierCompletion hC hcover hA hB g n hcomp,
    contactCompleteOrder_strong_intersections hC hcover hA hB hStrong hInter hShared⟩

end StructuralRamsey.Girth

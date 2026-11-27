import Girth.ContactRelationalUnion
import Girth.TreeSupport
import Girth.Berge

/-! The order-reduct corollary, separate from the recursive train
theorem. Completing the order need not preserve arbitrary copies:
the irreducibility of the NON-ORDER reduct forces each candidate
copy back into one original ordered B-copy. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W : Type v}
variable {C : RelStructure L.withOrder W} [LinearOrder W]

/-- Forgetting the added order from an embedding of a completed
ordered structure gives an induced embedding of the reducts. -/
def contactCompleteOrder_reduct
    {A : RelStructure L U} [LinearOrder U]
    (a : Embedding A.ordered C.completeOrder) : Embedding A C.orderReduct where
  toFun := a
  injective := a.injective
  map_rel_iff := fun R x => a.map_rel_iff (.inl R) x

/-- The range of an irreducible non-order source remains
irreducible even before the ambient order is completed. -/
theorem contactCompleteOrder_range_irreducible
    {A : RelStructure L U} [LinearOrder U] (hA : A.Irreducible)
    (a : Embedding A.ordered C.completeOrder) :
    (C.induce (Set.range a)).Irreducible := by
  let e := contactCompleteOrder_reduct a
  have h := hA.range_embedding e
  intro x y hxy
  -- The subtype carriers of the two ranges are definitionally equal.
  obtain ⟨R,z,i,j,hz,hi,hj⟩ := h hxy
  exact ⟨.inl R,z,i,j,hz,hi,hj⟩

/-- On the carrier of an original ordered B-copy, the completed
order adds no new order pair or relational tuple. -/
theorem contactCompleteOrder_rel_iff_on_copy
    {B : RelStructure L V} [LinearOrder V]
    (hC : C.ExtendsOrder) (b : Embedding B.ordered C)
    (R : L.withOrder.Symbol) (x : Fin (L.withOrder.arity R) → W)
    (hx : ∀ i, x i ∈ copyCarrier b) :
    C.completeOrder.rel R x ↔ C.rel R x := by
  classical
  cases R with
  | inl R => rfl
  | inr r =>
    have hex (i : Fin (L.withOrder.arity (.inr r))) : ∃ y : V, b y = x i := hx i
    choose y hy using hex
    have hEq : b.toFun ∘ y = x := funext hy
    rw [← hEq]
    exact ((b.completeOrder hC).map_rel_iff (.inr r) y).trans
      (b.map_rel_iff (.inr r) y).symm

/-- Every embedding of an ordered source with irreducible reduct
into the completed order is already an embedding into the
original relational union. This needs the B-cover hypothesis;
it is false for a pure ordered two-element source in general. -/
noncomputable def contactCompleteOrder_lift
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V]
    (hC : C.ExtendsOrder)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    (hA : A.Irreducible)
    (a : Embedding A.ordered C.completeOrder) :
    Embedding A.ordered C := by
  classical
  let hb := hcover (Set.range a) (contactCompleteOrder_range_irreducible hA a)
  let b := Classical.choose hb
  have hsub := Classical.choose_spec hb
  refine {toFun := a,injective := a.injective,map_rel_iff := ?_}
  intro R x
  have h := contactCompleteOrder_rel_iff_on_copy hC b R (a.toFun ∘ x)
    (fun i => hsub ⟨x i,rfl⟩)
  exact h.symm.trans (a.map_rel_iff R x)

/-- The actual embedding types before and after order completion
are equivalent; the underlying vertex maps are literally unchanged. -/
noncomputable def contactCompleteOrder_equiv
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V]
    (hC : C.ExtendsOrder)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    (hA : A.Irreducible) :
    Embedding A.ordered C ≃ Embedding A.ordered C.completeOrder where
  toFun := fun a => a.completeOrder hC
  invFun := contactCompleteOrder_lift hC hcover hA
  left_inv := fun a => Embedding.ext (fun _ => rfl)
  right_inv := fun a => Embedding.ext (fun _ => rfl)

theorem contactCompleteOrder_support_eq
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V]
    (hC : C.ExtendsOrder)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    (hA : A.Irreducible) :
    supportCopies A.ordered C.completeOrder = supportCopies A.ordered C := by
  ext S
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨contactCompleteOrder_lift hC hcover hA a,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨a.completeOrder hC,rfl⟩

theorem contactCompleteOrder_girth_arrow
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V]
    (hC : C.ExtendsOrder)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    (hA : A.Irreducible) (g : ℕ) (Color : Type v)
    (hG : GirthGT (supportCopies A.ordered C) g)
    (hArrow : StructuralRamsey.Arrow A.ordered B.ordered C Color) :
    GirthGT (supportCopies A.ordered C.completeOrder) g ∧
      StructuralRamsey.Arrow A.ordered B.ordered C.completeOrder Color := by
  constructor
  · rw [contactCompleteOrder_support_eq hC hcover hA]
    exact hG
  · exact RelStructure.arrow_completeOrder A B C hC Color hArrow

/-- If both reducts are irreducible, both actual copy families
and all their carrier intersections are preserved. -/
theorem contactCompleteOrder_strong_intersections
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V]
    (hC : C.ExtendsOrder)
    (hcover : ∀ S : Set W, (C.induce S).Irreducible →
      ∃ b : Embedding B.ordered C, S ⊆ copyCarrier b)
    (hA : A.Irreducible) (hB : B.Irreducible)
    (hStrong : ∀ b : Embedding B.ordered C, AStrong A.ordered C (copyCarrier b))
    (hInter : BIntersectionsControlled A.ordered B.ordered C)
    (hShared : BSingletonIntersectionsSupported A.ordered B.ordered C) :
    (∀ b : Embedding B.ordered C.completeOrder, AStrong A.ordered C.completeOrder (copyCarrier b)) ∧
      BIntersectionsControlled A.ordered B.ordered C.completeOrder ∧
      BSingletonIntersectionsSupported A.ordered B.ordered C.completeOrder := by
  let liftA := contactCompleteOrder_lift hC hcover hA
  let liftB := contactCompleteOrder_lift hC hcover hB
  refine ⟨?_,?_,?_⟩
  · intro b a hn
    exact hStrong (liftB b) (liftA a) hn
  · intro b c hn
    rcases hInter (liftB b) (liftB c) hn with hs | ⟨a,ha⟩
    · exact Or.inl hs
    · exact Or.inr ⟨a.completeOrder hC,ha⟩
  · intro b c hn hs x hx
    obtain ⟨⟨a,ha,ha'⟩,⟨d,hd,hd'⟩⟩ := hShared (liftB b) (liftB c) hn hs x hx
    exact ⟨⟨a.completeOrder hC,ha,ha'⟩,⟨d.completeOrder hC,hd,hd'⟩⟩

end StructuralRamsey.Girth

import Girth.Support
import PartiteConstruction.Relational.Order

set_option autoImplicit false

namespace StructuralRamsey.Girth

open RelStructure

universe u v
variable {L : RelLanguage.{u}} {U W : Type v}
variable {A : RelStructure L U} {C : RelStructure L.withOrder W}
variable [LinearOrder U] [LinearOrder W]

/-- The old order compares each pair of distinct vertices inside each copy of
the source in the order reduct. -/
def orderComparesCopies (A : RelStructure L U) (C : RelStructure L.withOrder W) : Prop :=
  ∀ (a : Embedding A C.orderReduct) (x y : U), x ≠ y →
    C.rel (.inr ()) ![a x, a y] ∨ C.rel (.inr ()) ![a y, a x]

/-- If the existing order compares each pair of distinct vertices of every
copy in the order reduct, completing it preserves exactly the embeddings of
the given ordered source. The ambient order need not be complete on other pairs. -/
def orderedEmbeddingsEquivCompleteOrder (hC : C.ExtendsOrder)
    (hCompare : orderComparesCopies A C) :
    Embedding A.ordered C ≃ Embedding A.ordered C.completeOrder where
  toFun := fun a => a.completeOrder hC
  invFun := fun a =>
    let reduct : Embedding A C.orderReduct := {
      toFun := a
      injective := a.injective
      map_rel_iff := fun r z => a.map_rel_iff (.inl r) z
    }
    { toFun := a
      injective := a.injective
      map_rel_iff := by
        intro r z
        cases r with
        | inl r => exact a.map_rel_iff (.inl r) z
        | inr r =>
            cases r
            change Fin 2 → U at z
            have hz : a ∘ z = ![a (z 0), a (z 1)] := by
              funext i
              fin_cases i <;> rfl
            let orderRel : (Fin 2 → W) → Prop :=
              fun pair => C.rel (Sum.inr () : L.withOrder.Symbol) pair
            change orderRel (a ∘ z) ↔ z 0 < z 1
            rw [hz]
            constructor
            · intro h
              exact a.strictMono.lt_iff_lt.mp (hC _ _ h)
            · intro h
              rcases hCompare reduct (z 0) (z 1) (ne_of_lt h) with hxy | hyx
              · exact hxy
              · exact (not_lt_of_ge (a.strictMono h).le (hC _ _ hyx)).elim }
  left_inv := by intro a; ext x; rfl
  right_inv := by intro a; ext x; rfl

/-- The literal supports, which serve as the train's edge labels, are the same
before and after completing a compatible order. -/
theorem supportCopies_completeOrder_eq (hC : C.ExtendsOrder)
    (hCompare : orderComparesCopies A C) :
    supportCopies A.ordered C.completeOrder = supportCopies A.ordered C := by
  let e := orderedEmbeddingsEquivCompleteOrder hC hCompare
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    exact ⟨e.symm a, rfl⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨e a, rfl⟩

end StructuralRamsey.Girth

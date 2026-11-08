import Girth.TrainSimultaneousSupreme

set_option autoImplicit false
set_option Elab.async false

/-!
# Exclude the two-physical-edge residual at source cycle length two

Every actual output BigCycle with two occurrences has two distinct
connectors and two different neighbouring labels. Under physical
pretrain linearity, TWO nondesignated labels (i.e. two genuine
physical edge labels) are incompatible with the order-one A1 condition:

* With two vertex connectors, the two distinct support edges would
  share both distinct vertices, contradicting physical edge linearity.
* With two wagon connectors, already one physical edge would have
  two distinct wagon parents, contradicting that parent is a function.
* With mixed connectors the cycle has twiceOrder=2, so A1 requires a
  designated occurrence.

This is the missing real n=2 owner-label classification; it does NOT
assert a global supreme plan for the remaining designated/core or
designated/designated cases. In particular it does not settle the
entire two-cut source transfer.
-/

namespace StructuralRamsey.Girth

universe v
variable {V E I P : Type v}

/-- At n=2, A1 together with physical edge linearity forces an ACTUAL
designated occurrence, even for a cycle whose manuscript order is 2
rather than 1. The argument does not identify equal-carrier labels,
invent a source standard, or change the actual connector word. -/
theorem OrderOneData.BigCycle.two_has_designated_of_linear
    (D : OrderOneData V E I P)
    (C : D.BigCycle 2)
    (hLinear : D.LinearPretrain)
    (hA1 : C.A1) :
    ∃ i : Fin 2, D.designated (C.label i) := by
  classical
  by_contra hNo
  have hSucc0 : cyclicSucc (0 : Fin 2) = 1 := by decide
  have hSucc1 : cyclicSucc (1 : Fin 2) = 0 := by decide
  have hDifferent : C.label (0 : Fin 2) ≠ C.label 1 := by
    simpa only [hSucc0] using C.adjacent_ne 0
  obtain ⟨e, he⟩ : ∃ e : E, C.label 0 = .inr e := by
    cases h : C.label (0 : Fin 2) with
    | inl a =>
      exact False.elim (hNo ⟨0, by simp [OrderOneData.designated, h]⟩)
    | inr e => exact ⟨e, h⟩
  obtain ⟨f, hf⟩ : ∃ f : E, C.label 1 = .inr f := by
    cases h : C.label (1 : Fin 2) with
    | inl a =>
      exact False.elim (hNo ⟨1, by simp [OrderOneData.designated, h]⟩)
    | inr f => exact ⟨f, h⟩
  have hef : e ≠ f := by
    intro h
    apply hDifferent
    rw [he, hf, h]
  have hDifferentConnectors : C.connector (0 : Fin 2) ≠ C.connector 1 := by
    intro h
    have h01 := C.connector_injective h
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  cases h0 : C.connector (0 : Fin 2) with
  | inl x =>
    cases h1 : C.connector (1 : Fin 2) with
    | inl y =>
      have hxy : x ≠ y := by
        intro h
        apply hDifferentConnectors
        rw [h0, h1, h]
      have hxE : x ∈ D.edgeCarrier e := by
        have h := C.left_incident (0 : Fin 2)
        rw [he, h0] at h
        exact h
      have hxF : x ∈ D.edgeCarrier f := by
        have h := C.right_incident (0 : Fin 2)
        rw [hSucc0, hf, h0] at h
        exact h
      have hyE : y ∈ D.edgeCarrier e := by
        have h := C.right_incident (1 : Fin 2)
        rw [hSucc1, he, h1] at h
        exact h
      have hyF : y ∈ D.edgeCarrier f := by
        have h := C.left_incident (1 : Fin 2)
        rw [hf, h1] at h
        exact h
      exact hxy ((hLinear.1 e f hef) ⟨hxE, hxF⟩ ⟨hyE, hyF⟩)
    | inr p =>
      have hOrder : C.twiceOrder = 2 := by
        simp [OrderOneData.BigCycle.twiceOrder, Fin.sum_univ_two,
          cyclicSucc, twiceOccurrenceWeight, connectorKind, h0, h1]
      exact hNo (hA1 hOrder)
  | inr p =>
    cases h1 : C.connector (1 : Fin 2) with
    | inl x =>
      have hOrder : C.twiceOrder = 2 := by
        simp [OrderOneData.BigCycle.twiceOrder, Fin.sum_univ_two,
          cyclicSucc, twiceOccurrenceWeight, connectorKind, h0, h1]
      exact hNo (hA1 hOrder)
    | inr q =>
      have hp : D.parent e = p := by
        have h := C.left_incident (0 : Fin 2)
        rw [he, h0] at h
        change D.Meets (.inr e) p at h
        obtain ⟨g, hg, hgp⟩ := h
        change g = e at hg
        subst g
        exact hgp
      have hq : D.parent e = q := by
        have h := C.right_incident (1 : Fin 2)
        rw [hSucc1, he, h1] at h
        change D.Meets (.inr e) q at h
        obtain ⟨g, hg, hgp⟩ := h
        change g = e at hg
        subst g
        exact hgp
      have hpq : p = q := hp.symm.trans hq
      apply hDifferentConnectors
      rw [h0, h1, hpq]

end StructuralRamsey.Girth

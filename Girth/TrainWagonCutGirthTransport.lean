import Girth.TrainWagonQuotientTransport
import Girth.LabelledWagonCutRestriction

/-!
# Exact labelled wagon-cut girth across physical edge isomorphisms

An edge bijection preserving the physical carrier of each edge
induces a bijection of horizontal wagon class labels with exactly
equal vertex carriers. Therefore even when distinct wagon labels
have identical carriers, every labelled Berge-cycle obstruction
transports in BOTH directions: all cut girth bounds are invariant.

This is the quantitative girth side of faithful representation
transport between the canonical picture edge pushout and genuine
A-support carriers. It is not preservation of system-Girth A1--A3
under new generated picture steps, nor does it justify edge pruning.
-/

namespace StructuralRamsey.Girth

universe v
variable {E F W : Type v}

namespace EdgeTrainLevels

/-- Every horizontal labelled wagon-cut girth bound is invariant
under a genuine carrier-preserving physical edge bijection. -/
theorem wagonTransport_labelledCutGirth_iff
    {m : ℕ} (T : EdgeTrainLevels E m)
    (ϕ : E ≃ F)
    (oldCarrier : E → Set W)
    (newCarrier : F → Set W)
    (hCarrier : ∀ e : E, newCarrier (ϕ e) = oldCarrier e)
    (μ : Fin (m + 1)) (g : ℕ) :
    LabelledGirthGT
      ((T.transport ϕ).wagonClassCarrier newCarrier μ) g ↔
    LabelledGirthGT
      (T.wagonClassCarrier oldCarrier μ) g := by
  let eqv := T.wagonTransportEquiv ϕ μ
  have hForward : ∀ q : Quotient (T.wagonSetoid μ),
      T.wagonClassCarrier oldCarrier μ q ⊆
        (T.transport ϕ).wagonClassCarrier newCarrier μ (eqv q) := by
    intro q
    have hEq := T.wagonTransport_carrier_eq
      ϕ oldCarrier newCarrier hCarrier μ q
    rw [hEq]
  have hBackward : ∀ q : Quotient ((T.transport ϕ).wagonSetoid μ),
      (T.transport ϕ).wagonClassCarrier newCarrier μ q ⊆
        T.wagonClassCarrier oldCarrier μ (eqv.symm q) := by
    intro q
    have hEq := T.wagonTransport_carrier_eq
      ϕ oldCarrier newCarrier hCarrier μ (eqv.symm q)
    have heq : eqv (eqv.symm q) = q := eqv.apply_symm_apply q
    rw [heq] at hEq
    rw [hEq]
  constructor
  · intro hNew
    exact labelledGirthGT_of_injective_shrinking
      ((T.transport ϕ).wagonClassCarrier newCarrier μ)
      (T.wagonClassCarrier oldCarrier μ)
      eqv eqv.injective hForward g hNew
  · intro hOld
    exact labelledGirthGT_of_injective_shrinking
      (T.wagonClassCarrier oldCarrier μ)
      ((T.transport ϕ).wagonClassCarrier newCarrier μ)
      eqv.symm eqv.symm.injective hBackward g hOld

end EdgeTrainLevels
end StructuralRamsey.Girth

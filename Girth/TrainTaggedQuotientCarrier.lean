import Girth.TrainGeneratedTagCarrierFibres
import Girth.TrainWagonClassRestriction

/-!
# Tagged source fibres are actual quotient wagon carriers

The shared/private source label representation uses tagged fibre unions.
These are definitionally the complete carriers of the true edge-relation
quotients. The result does not identify distinct classes having equal
carriers, and does not presume any bridge or train parameter bound.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I OldEdge CoreEdge : Type v}

/-- Full tagged old-wagon fibre equals its actual quotient-class carrier. -/
theorem taggedOldFiberCarrier_eq_wagonClassCarrier
    {m : ℕ} (T : EdgeTrainLevels OldEdge m)
    (edge : I → OldEdge → Set W) (μ : Fin (m + 1)) :
    taggedOldFiberCarrier (Quotient.mk (T.wagonSetoid μ)) edge =
      fun i => T.wagonClassCarrier (edge i) μ := by
  funext i u
  induction u using Quotient.inductionOn with
  | h a =>
    ext x
    change (∃ b : OldEdge,
        Quotient.mk (T.wagonSetoid μ) b =
          Quotient.mk (T.wagonSetoid μ) a ∧
        x ∈ edge i b) ↔
      (∃ b : OldEdge, T.rel μ a b ∧ x ∈ edge i b)
    constructor
    · rintro ⟨b, h, hx⟩
      exact ⟨b, (T.equivalent μ).symm (Quotient.exact h), hx⟩
    · rintro ⟨b, h, hx⟩
      exact ⟨b, Quotient.sound ((T.equivalent μ).symm h), hx⟩

/-- Full tagged core-wagon fibre equals its actual quotient-class carrier. -/
theorem taggedCoreFiberCarrier_eq_wagonClassCarrier
    {m : ℕ} (T : EdgeTrainLevels CoreEdge m)
    (edge : CoreEdge → Set W) (μ : Fin (m + 1)) :
    taggedCoreFiberCarrier (Quotient.mk (T.wagonSetoid μ)) edge =
      T.wagonClassCarrier edge μ := by
  funext u
  induction u using Quotient.inductionOn with
  | h a =>
    ext x
    change (∃ b : CoreEdge,
        Quotient.mk (T.wagonSetoid μ) b =
          Quotient.mk (T.wagonSetoid μ) a ∧
        x ∈ edge b) ↔
      (∃ b : CoreEdge, T.rel μ a b ∧ x ∈ edge b)
    constructor
    · rintro ⟨b, h, hx⟩
      exact ⟨b, (T.equivalent μ).symm (Quotient.exact h), hx⟩
    · rintro ⟨b, h, hx⟩
      exact ⟨b, Quotient.sound ((T.equivalent μ).symm h), hx⟩

end StructuralRamsey.Girth

import Mathlib.Tactic
import Mathlib.Data.Quot

/-! The common train hierarchy and its actual wagon quotient.
Extracted from TrainEquivalenceRestriction and TrainWagonClassRestriction;
the historical imports remain compatible. -/

namespace StructuralRamsey.Girth

universe v
variable {E : Type v}

/-- The equivalence-level data of a height-m train, with
explicit bottom equality, top universal class and nesting. -/
structure EdgeTrainLevels (E : Type v) (m : ℕ) where
  rel : Fin (m + 1) → E → E → Prop
  equivalent : ∀ μ, Equivalence (rel μ)
  nested : ∀ μ ν : Fin (m + 1), μ ≤ ν →
    ∀ e f : E, rel μ e f → rel ν e f
  bottom : ∀ e f : E,
    rel ⟨0, Nat.zero_lt_succ m⟩ e f ↔ e = f
  top : ∀ e f : E, rel ⟨m, Nat.lt_succ_self m⟩ e f

/-- The setoid whose classes are the μ-wagons of the edge train. -/
def EdgeTrainLevels.wagonSetoid
    {m : ℕ} (T : EdgeTrainLevels E m)
    (μ : Fin (m + 1)) : Setoid E where
  r := T.rel μ
  iseqv := T.equivalent μ

end StructuralRamsey.Girth

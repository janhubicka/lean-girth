import Girth.TrainRecursiveRefinementRetainedCutGirth

set_option autoImplicit false
set_option Elab.async false

/-!
# Track 6: simultaneous exact retained-cut transport

Unlike a proof that retains just the first cutoff, this theorem keeps
EVERY positive old labelled-cut cutoff at its own exact value. It is
independent of the new doubled-girth argument and of the construction
of a lower Ramsey witness.

All wagon labels remain quotients of the literal edge relation. No
two wagon classes are identified when they have the same carrier.
Only genuinely inserted lower cuts are omitted from this transport.

Candidate certificate: requires exact-head Lean elaboration and
#print axioms before declaring a new checked formal theorem.
-/

namespace StructuralRamsey.Girth

universe v
variable {E W P : Type v}
variable {m : ℕ} {T : EdgeTrainLevels E m} {hm : 0 < m}
variable {edge : E → Set W} {part : W → P}
variable {firstAllowed : Set P} {g : ℕ}

/-- Every retained positive horizontal cut keeps the literal old
cutoff, not the common lower g and not a uniform head cutoff. -/
theorem FirstWagonRefinement.allRetainedLabelledCutGirth
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (cutoff : Fin (m + 1) → ℕ)
    (hOld : ∀ μ : Fin (m + 1), 0 < μ.val →
      LabelledGirthGT (T.wagonClassCarrier edge μ) (cutoff μ)) :
    ∀ μ : Fin (m + 1), 0 < μ.val →
      LabelledGirthGT
        (R.train.wagonClassCarrier edge
          (EdgeTrainLevels.firstRefinementShift m R.extraCuts μ))
        (cutoff μ) := by
  intro μ hμ
  exact R.labelledGirthGT_at_retained μ hμ
    (cutoff μ) (hOld μ hμ)

/-- The same certificate allows each retained target cutoff to be
weakened individually, without losing stronger entries elsewhere. -/
theorem FirstWagonRefinement.allRetainedLabelledCutGirth_mono
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (oldCutoff newCutoff : Fin (m + 1) → ℕ)
    (hLe : ∀ μ, newCutoff μ ≤ oldCutoff μ)
    (hOld : ∀ μ : Fin (m + 1), 0 < μ.val →
      LabelledGirthGT (T.wagonClassCarrier edge μ) (oldCutoff μ)) :
    ∀ μ : Fin (m + 1), 0 < μ.val →
      LabelledGirthGT
        (R.train.wagonClassCarrier edge
          (EdgeTrainLevels.firstRefinementShift m R.extraCuts μ))
        (newCutoff μ) := by
  intro μ hμ
  exact R.labelledGirthGT_at_retained_mono μ hμ
    (oldCutoff μ) (newCutoff μ) (hLe μ) (hOld μ hμ)

end StructuralRamsey.Girth

#print axioms StructuralRamsey.Girth.FirstWagonRefinement.allRetainedLabelledCutGirth
#print axioms StructuralRamsey.Girth.FirstWagonRefinement.allRetainedLabelledCutGirth_mono

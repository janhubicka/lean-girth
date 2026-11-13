import Girth.TrainRecursiveSelectedLowerActualInputs
import Girth.TrainRecursiveExactHeightTransport

set_option autoImplicit false
set_option Elab.async false

/-!
# Canonical fine allowed parts under the actual recursive height equality

The genuine first-wagon refinement already supplies singleton inserted
parents, containment in the old first allowed set at all new positive
levels, and containment in the exact old allowed set at each retained
positive cut.  The recursion uses the literal lower cutoff-vector length
rather than the arithmetically equal old height plus extra cuts.

This transfers all THREE conditions simultaneously along that actual
equality, without introducing separate geometry assumptions, changing
the part sets, or forgetting the overlapping first retained parent.
-/

namespace StructuralRamsey.Girth

universe v
variable {E W P UA : Type v}

/-- All allowed-part clauses required by the lower refined attachment,
at exactly the lower replicated cutoff-vector height, are consequences
of the actual first-wagon refinement fields. -/
theorem FirstWagonRefinement.canonicalFineAllowed_castHeight_all_constraints
    {m : ℕ} {T : EdgeTrainLevels E m} {hm : 0 < m}
    {edge : E → Set W} {part : W → P} {g : ℕ}
    (oldAllowed : Fin (m + 1) → Set P)
    (R : FirstWagonRefinement T hm edge part
      (oldAllowed ⟨1, Nat.succ_lt_succ hm⟩) g)
    (α : UA ↪ P)
    {n : ℕ} (hLen : m + R.extraCuts = n) :
    let h := congrArg (fun k : ℕ => k + 1) hLen
    let fine : Fin (n + 1) → Set UA :=
      fun ρ => TrainRecursiveWitness.fineAllowedFromRefinement
        m R.extraCuts hm α oldAllowed R.permitted (Fin.cast h.symm ρ)
    (∀ j : Fin (R.extraCuts + 1),
      (fine (Fin.cast h
        (firstRefinementParent m R.extraCuts hm j))).Subsingleton) ∧
    (∀ ρ : Fin (n + 1), 0 < ρ.val → ρ.val ≤ R.extraCuts + 1 →
      fine ρ ⊆ α ⁻¹' oldAllowed ⟨1, Nat.succ_lt_succ hm⟩) ∧
    (∀ μ : Fin (m + 1), 0 < μ.val →
      fine (Fin.cast h
        (EdgeTrainLevels.firstForgetIndex m R.extraCuts μ)) ⊆
        α ⁻¹' oldAllowed μ) := by
  let h := congrArg (fun k : ℕ => k + 1) hLen
  let orig := TrainRecursiveWitness.fineAllowedFromRefinement
    m R.extraCuts hm α oldAllowed R.permitted
  let fine : Fin (n + 1) → Set UA :=
    fun ρ => orig (Fin.cast h.symm ρ)
  have hCancel (ρ : Fin (m + R.extraCuts + 1)) :
      Fin.cast h.symm (Fin.cast h ρ) = ρ := Fin.ext rfl
  obtain ⟨hSingleton, hFirst, hRetained⟩ :=
    R.canonicalFineAllowed_all_constraints oldAllowed α
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro j
    change (orig (Fin.cast h.symm
      (Fin.cast h (firstRefinementParent m R.extraCuts hm j)))).Subsingleton
    rw [hCancel]
    exact hSingleton j
  · intro ρ hp hle
    exact hFirst (Fin.cast h.symm ρ)
      (by simpa only [Fin.val_cast] using hp)
      (by simpa only [Fin.val_cast] using hle)
  · intro μ hp
    change orig (Fin.cast h.symm
      (Fin.cast h (EdgeTrainLevels.firstForgetIndex m R.extraCuts μ))) ⊆
      α ⁻¹' oldAllowed μ
    rw [hCancel]
    exact hRetained μ hp

end StructuralRamsey.Girth

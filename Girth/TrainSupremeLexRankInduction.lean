import Girth.TrainDesignatedLabelLexRank

set_option autoImplicit false
set_option Elab.async false

/-!
# Close the global supreme-cycle induction from actual lexicographic descent

The potential for the selected-output positive-cut argument is the
lexicographic pair
  (minimum geometric owner cuts, designated occurrence count).
The well-foundedness of this rank is already proved separately.

This module is the EXACT general logical induction principle. For
each acceptable bounded-order cycle it requires EITHER a complete
legal simultaneous supreme plan OR an actual acceptable bounded-order
output with strictly smaller rank and a proof that supremeness of
that output pulls back to the original cycle. It then derives the
FULL SupremeCycleBound, not merely a local-piece substitute.

The geometric hypothesis is deliberately explicit: this lemma
does not manufacture a minimal owner assignment, a reduced witness
cycle, a legal short/long replacement, a rank decrease, or the
order-one bridge case. Those are the remaining positive-cut tasks.
No appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A genuine well-founded descent step at the lexicographic rank
closes the full simultaneous-replacement girth predicate. The output
may have a different length: the induction compares physical cycles
by rank, not by cyclic index type or a phantom chosen standard. -/
theorem supremeCycleBound_of_lexDescent
    (q : ℕ)
    (rank : ∀ n : ℕ, D.BigCycle n → ℕ × ℕ)
    (step : ∀ {n : ℕ} (C : D.BigCycle n),
      C.Acceptable → C.twiceOrder ≤ 2 * q →
      C.HasSimultaneousSupreme ∨
        ∃ (m : ℕ) (H : D.BigCycle m),
          H.Acceptable ∧
          H.twiceOrder ≤ 2 * q ∧
          Prod.Lex (· < ·) (· < ·) (rank m H) (rank n C) ∧
          (H.HasSimultaneousSupreme → C.HasSimultaneousSupreme)) :
    D.SupremeCycleBound q := by
  have hAll : ∀ r : ℕ × ℕ,
      ∀ {n : ℕ} (C : D.BigCycle n),
        rank n C = r → C.Acceptable →
        C.twiceOrder ≤ 2 * q → C.HasSimultaneousSupreme := by
    apply natCutDesignatedLex_wellFounded.induction
    intro r ih n C hRank hAccept hOrder
    rcases step C hAccept hOrder with hSup | ⟨m, H, hAcceptH, hOrderH, hSmaller, hPull⟩
    · exact hSup
    · apply hPull
      have hBelow :
          Prod.Lex (· < ·) (· < ·) (rank m H) r := by
        rw [← hRank]
        exact hSmaller
      exact ih (rank m H) hBelow H rfl hAcceptH hOrderH
  intro n C hAccept hOrder
  exact hAll (rank n C) C rfl hAccept hOrder

/-- Adding the separately verified physical pretrain linearity gives
the FULL output system-girth certificate at this cutoff. -/
theorem fullSystemGirthGT_of_lexDescent
    (q : ℕ) (hLinear : D.LinearPretrain)
    (rank : ∀ n : ℕ, D.BigCycle n → ℕ × ℕ)
    (step : ∀ {n : ℕ} (C : D.BigCycle n),
      C.Acceptable → C.twiceOrder ≤ 2 * q →
      C.HasSimultaneousSupreme ∨
        ∃ (m : ℕ) (H : D.BigCycle m),
          H.Acceptable ∧
          H.twiceOrder ≤ 2 * q ∧
          Prod.Lex (· < ·) (· < ·) (rank m H) (rank n C) ∧
          (H.HasSimultaneousSupreme → C.HasSimultaneousSupreme)) :
    D.FullSystemGirthGT q :=
  ⟨hLinear, D.supremeCycleBound_of_lexDescent q rank step⟩

end StructuralRamsey.Girth.OrderOneData

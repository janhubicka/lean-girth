import Girth.TrainStrictPlanComplete
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# A genuine old length-two LONG yields a global simultaneous supreme plan

In an original two-occurrence BigCycle there is exactly one occurrence
other than a chosen designated target. Once a real ShortValid or
LongValid piece is found at that other occurrence, the global
PlanValid proof has no interactions between distinct replacements.
For a LongValid piece, BOTH original connectors are genuine vertices;
the long piece's internal wagon is therefore automatically fresh.

The fully checked all-length strict-plan completion then constructs
a genuine cyclic BigCycle with the literal replacement word (including
the wrap and the A1--A3/order certificates). There is no assumption
that a merely local piece automatically becomes a global plan.

This is the missing global leg of the original length-two no-pair
LONG alternative; the physical LongValid ownership has to be
derived separately from the actual two-cut witness geometry.
It is independent of a purported output FullSystemGirthGT.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- An actual long at the non-target position of a two-cycle cannot
reuse an original wagon connector, since its two boundary connectors
are both literal vertices. -/
theorem BigCycle.two_long_fresh
    (Z : D.BigCycle 2) (k : Fin 2)
    (e : E) (w : P) (f : E)
    (hLong : Z.LongValid D k (cyclicSucc k) e w f) :
    ∀ t : Fin 2, Z.connector t ≠ Sum.inr w := by
  rcases hLong with ⟨x, y, hx, hy, _he, _hf, _hne,
    _hpe, _hpf, _hxe, _hyf, _hPair⟩
  have hPred : trainCyclicPred (cyclicSucc k) = k := by
    fin_cases k <;> decide
  have hk : Z.connector k = Sum.inl x := by
    simpa only [hPred] using hx
  have hs : Z.connector (cyclicSucc k) = Sum.inl y := hy
  intro t
  have ht : t = k ∨ t = cyclicSucc k := by
    fin_cases k <;> fin_cases t <;> simp [cyclicSucc]
  rcases ht with ht | ht
  · rw [ht, hk]
    intro h
    cases h
  · rw [ht, hs]
    intro h
    cases h

/-- At source length two, ANY chosen non-keep piece satisfying its
actual ShortValid/LongValid predicate and fresh-wagon condition makes
a complete simultaneous indexed supreme plan. Not just a local
piece: the genuine expanded cyclic word is constructed by the
already verified strict-plan theorem. -/
theorem BigCycle.two_hasSupremeAt_of_local_piece
    (Z : D.BigCycle 2)
    (hAccept : Z.Acceptable)
    (hLinear : D.LinearPretrain)
    (k : Fin 2) (hk : D.designated (Z.label k))
    (piece : TrainSupremePiece E P)
    (hLocal :
      match piece with
      | .keep => False
      | .short e => Z.ShortValid D k (cyclicSucc k) e
      | .long e w f => Z.LongValid D k (cyclicSucc k) e w f)
    (hFreshPiece : ∀ (e : E) (w : P) (f : E),
      piece = .long e w f →
      ∀ t : Fin 2, Z.connector t ≠ Sum.inr w) :
    Z.HasSupremeAt D k := by
  classical
  let pieces : Fin 2 → TrainSupremePiece E P :=
    fun j => if j = k then .keep else piece
  have hPlan : Z.PlanValid D k pieces := by
    intro j
    by_cases hj : j = k
    · subst j
      constructor
      · intro _
        simp [pieces]
      · intro h
        exact (h rfl).elim
    · have hOther : j = cyclicSucc k := by
        fin_cases j <;> fin_cases k <;>
          simp_all [cyclicSucc]
      have hDifferent : Z.label j ≠ Z.label k := by
        rw [hOther]
        exact (Z.adjacent_ne k).symm
      constructor
      · intro hSame
        exact (hDifferent hSame).elim
      · intro _
        have hPiece : pieces j = piece := by
          simp [pieces, hj]
        have hLocalJ :
            match piece with
            | .keep => False
            | .short e => Z.ShortValid D k j e
            | .long e w f => Z.LongValid D k j e w f := by
          simpa only [hOther] using hLocal
        simpa only [hPiece] using hLocalJ
  have hFresh : ∀ (j : Fin 2) (e : E) (w : P) (f : E),
      pieces j = .long e w f →
      ∀ t : Fin 2, Z.connector t ≠ Sum.inr w := by
    intro j e w f hLong t
    by_cases hj : j = k
    · have hp : pieces j = .keep := by simp [pieces, hj]
      rw [hp] at hLong
      cases hLong
    · have hp : pieces j = piece := by simp [pieces, hj]
      rw [hp] at hLong
      exact hFreshPiece e w f hLong t
  obtain ⟨m, B, _hAcceptB, _hOrderB, hWord⟩ :=
    Z.planProducesAcceptableOrder_all_lengths D
      hAccept hLinear k hk pieces hPlan hFresh
  exact ⟨hk, pieces, hPlan, ⟨m, B, hWord⟩⟩

/-- A REAL LongValid through two source vertices, including a
no-pair condition and two distinct physical edges in the same
wagon, gives FULL global indexed supremeness at length two.
The long's own validity makes its wagon freshness automatic. -/
theorem BigCycle.two_hasSupremeAt_of_long
    (Z : D.BigCycle 2)
    (hAccept : Z.Acceptable)
    (hLinear : D.LinearPretrain)
    (k : Fin 2) (hk : D.designated (Z.label k))
    (e : E) (w : P) (f : E)
    (hLong : Z.LongValid D k (cyclicSucc k) e w f) :
    Z.HasSupremeAt D k := by
  apply Z.two_hasSupremeAt_of_local_piece
    D hAccept hLinear k hk (.long e w f) hLong
  intro e' w' f' heq t
  cases heq
  exact Z.two_long_fresh D k e w f hLong t

/-- Forgetting the chosen original designated index gives the usual
fully simultaneous supreme certificate (not merely local pieces). -/
theorem BigCycle.two_hasSimultaneousSupreme_of_long
    (Z : D.BigCycle 2)
    (hAccept : Z.Acceptable)
    (hLinear : D.LinearPretrain)
    (k : Fin 2) (hk : D.designated (Z.label k))
    (e : E) (w : P) (f : E)
    (hLong : Z.LongValid D k (cyclicSucc k) e w f) :
    Z.HasSimultaneousSupreme := by
  exact Z.hasSimultaneousSupreme_of_hasSupremeAt D k
    (Z.two_hasSupremeAt_of_long D hAccept hLinear k hk e w f hLong)

end StructuralRamsey.Girth.OrderOneData

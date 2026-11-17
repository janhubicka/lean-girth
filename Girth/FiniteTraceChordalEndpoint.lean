import Girth.FiniteTracePEOCount
import Girth.FiniteTraceCycleGraphFacts

/-!
# Exact Track 8 local-completion to no-induced-cycle endpoint

An induced k-cycle on the finite tested vertex type Z has k distinct
vertices. Hence k <= |Z| <= q, so the indexed cycle obstruction
can be applied without a separate arithmetic budget hypothesis.

The FULL small-trace conclusion is then conditional on exactly
one standard finite graph theorem: every finite graph with no
induced cycles of length at least four has a perfect elimination order.
This theorem is not assumed globally or installed as an axiom here;
its application is explicitly a hypothesis of the last theorem.

This file does not yet certify the Dirac/chordal-to-PEO implication.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Absence of induced chordless cycles of length at least four.
A plain (not induced) graph cycle is intentionally insufficient. -/
def NoLongInducedCycles (G : SimpleGraph W) : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    ∀ v : Fin k → W, ¬ IsInducedFinCycle G k v

/-- Bounded internal completion of original cover members excludes
all induced cycles of length >= 4 in the trace pair graph.
The budget k<=q is automatic from injectivity of the cycle map. -/
theorem tracePairGraph_noLongInducedCycles_of_local
    [Fintype W] [Fintype ι]
    (F : ι → Set W) (Z : Set W) (q : ℕ)
    (hLocal : HasInternalJoinTreeCompletions F q)
    (hBudget : Z.ncard ≤ q) :
    NoLongInducedCycles (tracePairGraph F Z) := by
  classical
  letI : Fintype Z := Fintype.ofFinite _
  intro k hk v hInduced
  have hkCard : k ≤ Fintype.card Z := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_le_of_injective v hInduced.1)
  have hkBudget : k ≤ q := by
    calc
      k ≤ Fintype.card Z := hkCard
      _ = Z.ncard := Set.fintypeCard_eq_ncard Z
      _ ≤ q := hBudget
  exact no_bounded_induced_trace_cycle
    F Z q k hLocal hk hkBudget v hInduced

/-- The sharp small-trace conclusion from the original bounded
internal completions, using just ONE explicitly supplied external
graph implication (finite chordal graph -> PEO).

The extra hypothesis is NOT an axiom or a claimed result.
It is the precise remaining strong-Dirac lemma to formalize. -/
theorem smallTrace_selection_of_local_and_chordalToPEO
    [Fintype W] [Fintype ι]
    (F : ι → Set W) (Z : Set W) (q : ℕ)
    (hCover : ∀ x : W, x ∈ Z → ∃ i : ι, x ∈ F i)
    (hLocal : HasInternalJoinTreeCompletions F q)
    (hBudget : Z.ncard ≤ q)
    (hChordalToPEO :
      NoLongInducedCycles (tracePairGraph F Z) →
        ∃ order : LinearOrder Z,
          @IsPerfectEliminationOrder Z order (tracePairGraph F Z)) :
    ∃ selected : Set ι,
      CoversNonemptyTraces F Z selected ∧
      selected.ncard ≤ Z.ncard := by
  have hNoCycles :=
    tracePairGraph_noLongInducedCycles_of_local
      F Z q hLocal hBudget
  obtain ⟨order, hPEO⟩ := hChordalToPEO hNoCycles
  letI : LinearOrder Z := order
  exact smallTrace_selection_of_local_completions_and_PEO
    F Z q hCover hLocal hBudget hPEO

end StructuralRamsey.Girth

import Girth.FiniteTraceDirac
import Girth.FiniteTracePEOCount
import Girth.FiniteTraceCycleGraphFacts

/-!
# Exact Track 8 local-completion to no-induced-cycle endpoint

An induced k-cycle on the finite tested vertex type Z has k distinct
vertices. Hence k <= |Z| <= q, so the indexed cycle obstruction
can be applied without a separate arithmetic budget hypothesis.

Dirac's theorem supplies a perfect elimination order of the trace graph.
Counting maximal traces by their first vertices gives the required
selection of original cover members.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

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

The precise finite graph implication is supplied below by Dirac's theorem. -/
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

/-- The selected original cover members from the bounded internal completions. -/
theorem smallTrace_selection_of_local_completions
    {W ι : Type*} [Fintype W] [Fintype ι]
    (F : ι → Set W) (Z : Set W) (q : ℕ)
    (hCover : ∀ x : W, x ∈ Z → ∃ i : ι, x ∈ F i)
    (hLocal : HasInternalJoinTreeCompletions F q)
    (hBudget : Z.ncard ≤ q) :
    ∃ selected : Set ι, CoversNonemptyTraces F Z selected ∧
      selected.ncard ≤ Z.ncard := by
  classical
  letI : Fintype Z := Fintype.ofFinite _
  exact smallTrace_selection_of_local_and_chordalToPEO
    F Z q hCover hLocal hBudget
    exists_perfectEliminationOrder_of_noLongInducedCycles

end StructuralRamsey.Girth

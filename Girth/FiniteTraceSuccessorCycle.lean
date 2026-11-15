import Girth.FiniteTraceChordlessPattern

/-!
# Chordless cycles indexed by a fixed-point-free successor permutation

This removes the two awkward "other edge through this endpoint"
assumptions from the cyclic-pairs obstruction.  For an edge
e = {v e, v (next e)}, the next edge contains the right endpoint,
and the preceding edge next.symm e contains the left endpoint.

We need no predecessor arithmetic on Fin n, and no assumption
that the successor permutation consists of a single orbit:
any such chordless pair system already contradicts bounded
original-cover local join-tree completions.

A cyclic-order / SimpleGraph.Walk API adapter for standard induced
cycles is still a separate obligation.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι E : Type v}

/-- A fixed-point-free successor permutation whose consecutive
vertex pairs are edges of the trace graph, and for which the
union of any two distinct required edges contains a nonedge,
is incompatible with local internal tree completion. -/
theorem no_bounded_chordless_successor_cycle
    [Fintype ι] [Fintype E] [Nonempty E]
    (F : ι → Set W) (Z : Set W) (q : ℕ)
    (hLocal : HasInternalJoinTreeCompletions F q)
    (next : E ≃ E)
    (hNoFix : ∀ e : E, next e ≠ e)
    (v : E → Z)
    (hCard : Fintype.card E ≤ q)
    (hEdges :
      ∀ e : E, (tracePairGraph F Z).Adj
        (v e) (v (next e)))
    (hCross :
      ∀ e f : E, e ≠ f →
        CrossPairNonedge (tracePairGraph F Z)
          v (fun e => v (next e)) e f) :
    False := by
  classical
  let e₀ : E := Classical.choice (inferInstance : Nonempty E)
  let e₁ : E := next e₀
  have he : e₀ ≠ e₁ := (hNoFix e₀).symm
  have hOtherA :
      ∀ e : E, ∃ f : E, f ≠ e ∧
        (v f = v e ∨ v (next f) = v e) := by
    intro e
    have hPredNe : next.symm e ≠ e := by
      intro h
      have heq := congrArg next h
      have heq' : e = next e := by
        simpa only [next.apply_symm_apply] using heq
      exact (hNoFix e) heq'.symm
    refine ⟨next.symm e, hPredNe, Or.inr ?_⟩
    simpa only [next.apply_symm_apply]
  have hOtherB :
      ∀ e : E, ∃ f : E, f ≠ e ∧
        (v f = v (next e) ∨
          v (next f) = v (next e)) := by
    intro e
    exact ⟨next e, hNoFix e, Or.inl rfl⟩
  exact no_bounded_chordless_pair_pattern
    F Z q hLocal v (fun e => v (next e))
    e₀ e₁ he hCard hOtherA hOtherB hEdges hCross

end StructuralRamsey.Girth

import Girth.ForestCompletionTransport

/-! # The quantified finite forest-completion invariant

The circulation manuscript's completion property quantifies over *every*
small finite family of tested A- or designated B-members.  The existential
completed family must be finite, contain all tested members, and add only
permitted designated B-members.  This is the abstract support-piece version,
independent of the A/B relational packaging.

Transporting this quantified property into one fresh standard copy is a
separate, generic step.  The rest of the picture construction must cover
families meeting several standard copies by gluing their local completions.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Z : Type v}

/-- Every finite tested family of cardinality at most m has a finite forest
completion with only designated extra pieces. -/
def ForestCompletionProperty
    (tested designated : HypergraphPiece W → Prop)
    (m : ℕ) : Prop :=
  ∀ (N : Type v) [Fintype N],
    ∀ (selected : N → HypergraphPiece W),
      (∀ n : N, tested (selected n)) →
      Fintype.card N ≤ m →
      ∃ (K : Type v), ∃ (finite : Fintype K),
        letI : Fintype K := finite
        ∃ completed : K → HypergraphPiece W,
          ForestCompletionWitness selected designated completed

/-- Completion invariance inside one transported standard picture.  Tested
pieces in its image are assumed to admit source preimages; designated old
pieces must transport to designated new pieces. -/
theorem ForestCompletionProperty.map
    {testedOld designatedOld : HypergraphPiece W → Prop}
    (hOld : ForestCompletionProperty testedOld designatedOld m)
    (φ : W ↪ Z)
    (testedNew designatedNew : HypergraphPiece Z → Prop)
    (hTestPullback :
      ∀ T : HypergraphPiece Z, testedNew T →
        ∃ S : HypergraphPiece W,
          testedOld S ∧ T = S.map φ)
    (hDesignated :
      ∀ S : HypergraphPiece W, designatedOld S →
        designatedNew (S.map φ)) :
    ForestCompletionProperty testedNew designatedNew m := by
  classical
  intro N hFinite selected hTest hCard
  letI : Fintype N := hFinite
  have hEach (n : N) :
      ∃ S : HypergraphPiece W,
        testedOld S ∧ selected n = S.map φ :=
    hTestPullback (selected n) (hTest n)
  choose source hSource hMap using hEach
  obtain ⟨K, finite, completed, hWitness⟩ :=
    hOld N source hSource hCard
  refine ⟨K, finite, ?_⟩
  letI : Fintype K := finite
  refine ⟨(fun k : K => (completed k).map φ), ?_⟩
  have hMapped :
      ForestCompletionWitness
        (fun n : N => (source n).map φ)
        designatedNew
        (fun k : K => (completed k).map φ) :=
    hWitness.map φ designatedNew hDesignated
  have hSelectedEq :
      (fun n : N => (source n).map φ) = selected := by
    funext n
    exact (hMap n).symm
  rw [hSelectedEq] at hMapped
  exact hMapped

end StructuralRamsey.Girth

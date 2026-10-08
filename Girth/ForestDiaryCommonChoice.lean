import Girth.ForestNeutralGap
import Mathlib.Tactic

/-!
# Compatible neutral codes at a finite history boundary

For a finite marked family, a common one-gap shape map requires that
histories with the same stem at the chosen insertion level prescribe
the same neutral transition code. This is a purely finite interface:
there is a single global choice function precisely when the prescribed
codes are consistent along equal boundary prefixes.

The theorem neither asserts that all geometrically relevant gaps are
neutral nor supplies the global carrier-faithful evaluation of a
Ramsey witness.
-/

namespace StructuralRamsey.Girth

universe u v

/-- A globally defined transition choice with prescribed values exists
if and only if those values agree on every fibre of the stem map.
The finite-index version is used for marked q-tuples, but the proof
needs only classical choice, not a cardinality bound. -/
theorem finiteHistoryCompatibleChoice_iff
    {α : Type u} {β : Type v} [Nonempty β]
    (q : ℕ) (stem : Fin q → α) (code : Fin q → β) :
    (∃ choose : α → β, ∀ i : Fin q,
        choose (stem i) = code i) ↔
      (∀ i j : Fin q, stem i = stem j →
        code i = code j) := by
  classical
  constructor
  · rintro ⟨choose, hChoose⟩ i j hij
    calc
      code i = choose (stem i) := (hChoose i).symm
      _ = choose (stem j) := congrArg choose hij
      _ = code j := hChoose j
  · intro hConsistent
    let choose : α → β :=
      fun a =>
        if h : ∃ i : Fin q, stem i = a then
          code (Classical.choose h)
        else
          Classical.choice (inferInstance : Nonempty β)
    refine ⟨choose, ?_⟩
    intro i
    have hi : ∃ j : Fin q, stem j = stem i :=
      ⟨i, rfl⟩
    change
      (if h : ∃ j : Fin q, stem j = stem i then
        code (Classical.choose h)
       else Classical.choice (inferInstance : Nonempty β)) = code i
    rw [dif_pos hi]
    exact hConsistent (Classical.choose hi) i
      (Classical.choose_spec hi)

/-- A specifically chosen q-tuple of successor codes can be replayed
by one common choice function whenever its stem-to-code relation is
functional. This is the useful implication direction. -/
theorem exists_commonNeutralGapChoice
    {Label : Type u} [Nonempty Label]
    (arity m q : ℕ)
    (stem : Fin q →
      SuccessorTree.FreeAncestral.History Label arity m)
    (code : Fin q →
      SuccessorTree.FreeAncestral.Code Label arity m)
    (h : ∀ i j : Fin q,
      stem i = stem j → code i = code j) :
    ∃ choose :
      SuccessorTree.FreeAncestral.History Label arity m →
        SuccessorTree.FreeAncestral.Code Label arity m,
      ∀ i : Fin q, choose (stem i) = code i := by
  exact (finiteHistoryCompatibleChoice_iff q stem code).2 h

end StructuralRamsey.Girth

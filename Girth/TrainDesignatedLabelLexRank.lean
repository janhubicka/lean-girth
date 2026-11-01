import Girth.TrainSimultaneousSupreme
import Mathlib.Tactic

/-!
# A target-independent secondary rank for designated long insertions

A long piece replacing one original designated B-copy label inserts two
PHYSICAL edge labels; its literal output has no new designated label.
Thus the total number of designated occurrences falls, regardless of
which supreme standard supplied the replacement.

The ordinary geometric owner cut count may stay equal in the non-
neighbour case, so an alternative rank is the lexicographic pair:
  (minimum geometric owner cuts, number of designated occurrence labels).
The elementary list identity and well-founded lex relation below are
valid without a fixed chosen supreme target. This is NOT a full Path A
induction: one must establish the actual output word decomposition,
admissible owner transport, and handle physical-edge short changes
which may preserve both components. No appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {I E : Type v}

/-- The count of genuine designated (left-injection) occurrences in
a literal list of labels. Source-carrier provenance does NOT affect it. -/
noncomputable def designatedLabelCount (labels : List (I ⊕ E)) : ℕ := by
  classical
  exact (labels.filter fun x => match x with
    | Sum.inl _ => True
    | Sum.inr _ => False).length

/-- One designated label replaced by TWO physical edges drops
the designated-label count by exactly one. Source and target
designated-copy identities are irrelevant. -/
theorem designatedLabelCount_long_insert_drop
    (before after : List (I ⊕ E))
    (source : I) (first second : E) :
    designatedLabelCount
      (before ++ Sum.inr first :: Sum.inr second :: after) + 1 =
      designatedLabelCount
        (before ++ Sum.inl source :: after) := by
  classical
  simp [designatedLabelCount, List.filter_append] <;> omega

/-- The same target-independent count drop holds for a SHORT
replacement of a designated original occurrence by a physical edge. -/
theorem designatedLabelCount_short_replace_drop
    (before after : List (I ⊕ E))
    (source : I) (edge : E) :
    designatedLabelCount (before ++ Sum.inr edge :: after) + 1 =
      designatedLabelCount (before ++ Sum.inl source :: after) := by
  classical
  simp [designatedLabelCount, List.filter_append] <;> omega

/-- For a well-founded lexicographic rank, NONINCREASING first
coordinate and STRICTLY decreasing second coordinate are enough.
This is the exact situation expected in a designated singleton long
insertion, even if the receiving standard is not a neighbour. -/
theorem natCutDesignatedLex_drop
    {oldCuts newCuts oldDesignated newDesignated : ℕ}
    (hCuts : newCuts ≤ oldCuts)
    (hDesignated : newDesignated < oldDesignated) :
    Prod.Lex (· < ·) (· < ·)
      (newCuts, newDesignated) (oldCuts, oldDesignated) := by
  rcases lt_or_eq_of_le hCuts with hLt | hEq
  · exact Prod.Lex.left _ _ hLt
  · subst newCuts
    exact Prod.Lex.right _ hDesignated

/-- The proposed target-INDEPENDENT rank is well-founded. Its
application requires a verified actual cycle comparison, not merely
these formal arithmetic lemmas. -/
theorem natCutDesignatedLex_wellFounded :
    WellFounded (Prod.Lex (· < ·) (· < ·) :
      (ℕ × ℕ) → (ℕ × ℕ) → Prop) :=
  WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf

end StructuralRamsey.Girth

import Girth.ForestDiaryMultiGap
import Mathlib.Tactic

/-!
# Locally checkable neutral-gap evidence for selected histories

The original MarkedNeutralGap certificate quantifies over every possible
global code-choice function agreeing at the retained prefix. This module
replaces that universal compatibility condition by a direct inductive
record of the *actual target codes*:

* one specified inserted code at the prefix stem; and
* every later code avoids naming that deleted target level as a parameter.

The local certificate gives the global one-gap shape map simultaneously
for any finite number of marked histories, once copies with the same
prefix prescribe the same inserted code.

This removes a syntactic certification burden; it does not establish
that actual train histories satisfy the gap assumptions, nor the
carrier-faithful evaluation of the compressed geometric records.
-/

namespace StructuralRamsey.Girth

open SuccessorTree
open SuccessorTree.FreeAncestral

universe u

/-- Entirely local information on a chosen history: the recorded inserted
successor at level m and the absence of later references to that level.
No global choice function is part of this predicate. -/
inductive LocalNeutralGapTail {Label : Type u} {arity : ℕ}
    (m : ℕ)
    (stem : History Label arity m)
    (insertedCode : Code Label arity m) :
    (k : ℕ) → History Label arity (m + k + 1) → Prop where
  | base :
      LocalNeutralGapTail m stem insertedCode 0
        (History.step stem insertedCode)
  | step {k : ℕ} {hist : History Label arity (m + k + 1)}
      (hprev : LocalNeutralGapTail m stem insertedCode k hist)
      (code : Code Label arity (m + k + 1))
      (hAvoid : ∀ j : Fin code.params.len.val,
        (code.params.value j).val ≠ m) :
      LocalNeutralGapTail m stem insertedCode (k + 1)
        (History.step hist code)

/-- A locally checked code record yields the original globally
choice-independent MarkedNeutralGap certificate. -/
def LocalNeutralGapTail.toMarkedNeutralGap
    {Label : Type u} {arity : ℕ}
    [Fintype Label] [Nonempty Label]
    {m k : ℕ}
    {stem : History Label arity m}
    {insertedCode : Code Label arity m}
    {hist : History Label arity (m + k + 1)}
    (hLocal : LocalNeutralGapTail m stem insertedCode k hist) :
    MarkedNeutralGap (Label := Label) (arity := arity) m k := by
  refine
    { history := hist
      stem := stem
      insertedCode := insertedCode
      compatible := ?_ }
  intro choose hc
  induction hLocal with
  | base =>
      change NeutralGapTail m choose 0
        (History.step stem insertedCode)
      rw [← hc]
      exact NeutralGapTail.base stem
  | step hprev code hAvoid ih =>
      exact NeutralGapTail.step ih code hAvoid

/-- Conversely, an existing global gap-tail proof yields a local
certificate recording its actual insertion code. -/
theorem exists_localNeutralGapTail_of_global
    {Label : Type u} {arity : ℕ} [Fintype Label]
    (m : ℕ)
    (choose : History Label arity m → Code Label arity m) :
    ∀ {k : ℕ} {hist : History Label arity (m + k + 1)},
      NeutralGapTail m choose k hist →
      ∃ stem : History Label arity m,
        LocalNeutralGapTail m stem (choose stem) k hist := by
  intro k hist h
  induction h with
  | base stem =>
      exact ⟨stem, .base⟩
  | step hprev code hAvoid ih =>
      obtain ⟨stem, hStem⟩ := ih
      exact ⟨stem, .step hStem code hAvoid⟩

/-- A finite family of purely *local* code certificates induces one
actual global one-gap map. The only coordination needed is that
equal marked prefixes prescribe equal insertion codes. -/
theorem finiteLocalNeutralGap_preimages
    {Label : Type u} {arity : ℕ}
    [Fintype Label] [Nonempty Label]
    (m k q : ℕ)
    (stem : Fin q → History Label arity m)
    (insertedCode : Fin q → Code Label arity m)
    (target : Fin q → History Label arity (m + k + 1))
    (hLocal : ∀ i : Fin q,
      LocalNeutralGapTail m (stem i) (insertedCode i) k (target i))
    (hConsistent : ∀ i j : Fin q, stem i = stem j →
      insertedCode i = insertedCode j) :
    ∃ choose : History Label arity m → Code Label arity m,
      ∃ source : Fin q → History Label arity (m + k),
        ∀ i : Fin q,
          gapNode m choose
            (⟨m + k, source i⟩ : Node Label arity) =
            (⟨m + k + 1, target i⟩ : Node Label arity) := by
  let P : Fin q →
      MarkedNeutralGap (Label := Label) (arity := arity) m k :=
    fun i => (hLocal i).toMarkedNeutralGap
  have hSame (i j : Fin q)
      (hStem : (P i).stem = (P j).stem) :
      (P i).insertedCode = (P j).insertedCode := by
    change insertedCode i = insertedCode j
    apply hConsistent i j
    exact hStem
  obtain ⟨choose, source, hMaps⟩ :=
    finiteMarkedNeutralGap_preimages m k q P hSame
  exact ⟨choose, source, hMaps⟩

end StructuralRamsey.Girth

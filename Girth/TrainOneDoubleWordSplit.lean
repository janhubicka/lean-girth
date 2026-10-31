import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Exact Fin-index splitting of one doubled occurrence in a literal word

For any Fin-indexed label word and selected position j, a list of
singleton blocks except one two-element block has the form of the
original label word with exactly the jth entry replaced by a,b.

This is the index-theoretic ingredient needed to turn the
target-independent designated-count rank into a theorem about
BigCycle.resultWord. The proof is by finite-index induction with
explicit treatment of the new first position, and does not assume
an output BigCycle or any geometric hypotheses. No appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {α : Type v}

/-- A typed one-to-two replacement list obtained by flattening a
Fin-indexed family of blocks. -/
def oneDoubleWord {n : ℕ}
    (labels : Fin n → α) (j : Fin n) (a b : α) : List α :=
  (List.ofFn fun k : Fin n =>
    if k = j then [a,b] else [labels k]).flatten

/-- The source and its one-double replacement admit the SAME exact
prefix and suffix, including replacement at index zero and the
last index. -/
theorem oneDoubleWord_exists_common_split
    {n : ℕ} (labels : Fin n → α) (j : Fin n) (a b : α) :
    ∃ (before after : List α),
      List.ofFn labels = before ++ labels j :: after ∧
      oneDoubleWord labels j a b = before ++ a :: b :: after := by
  induction n generalizing labels j with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      cases j using Fin.cases with
      | zero =>
          refine ⟨[], List.ofFn (fun k : Fin n => labels k.succ), ?_, ?_⟩
          · simp [List.ofFn_succ]
          · simp [oneDoubleWord, List.ofFn_succ]
      | succ j =>
          obtain ⟨before, after, hOld, hNew⟩ :=
            ih (fun k : Fin n => labels k.succ) j
          refine ⟨labels 0 :: before, after, ?_, ?_⟩
          · simp only [List.ofFn_succ, List.cons_append]
            exact congrArg (List.cons (labels 0)) hOld
          · have hBlocks :
                oneDoubleWord labels (Fin.succ j) a b =
                labels 0 :: oneDoubleWord
                  (fun k : Fin n => labels k.succ) j a b := by
                simp [oneDoubleWord, List.ofFn_succ]
            rw [hBlocks, hNew]
            simp [List.cons_append]

end StructuralRamsey.Girth

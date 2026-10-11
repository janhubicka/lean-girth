import Girth.TrainCutoffLexRank
import Mathlib.Order.RelClasses

/-!
# Well-founded multiplicity lexicographic train cutoff recursion

The finite train induction uses multiplicities at cutoffs from largest
to smallest. Replacing a cutoff q>2 by an arbitrarily large number of
q-1 coordinates still decreases this lexicographic rank; a fixed
natural weighted sum need not decrease.

For every finite bound M, the nested lexicographic product of
natural-number multiplicities at levels M,...,1 is well-founded.
The checked q>2 replacement and q=2 deletion preserve all higher
multiplicities and strictly decrease the changed one.

This proves the actual termination ORDER for the recursion. It
does not construct the witnesses or prove their train invariants.
-/

namespace StructuralRamsey.Girth

/-- Compare cutoff vectors by their multiplicities, from M down. -/
def TrainCountLex : ℕ → List ℕ → List ℕ → Prop
  | 0, _, _ => False
  | M+1, s, t =>
      Prod.Lex (· < ·) (TrainCountLex M)
        (countTrainCutoff s (M+1), s)
        (countTrainCutoff t (M+1), t)

/-- Finite nested lexicographic products of natural counts are well-founded. -/
theorem trainCountLex_wellFounded (M : ℕ) :
    WellFounded (TrainCountLex M) := by
  induction M with
  | zero =>
      apply WellFounded.intro
      intro t
      apply Acc.intro
      intro s hs
      exact False.elim hs
  | succ M ih =>
      change WellFounded (fun s t : List ℕ =>
        Prod.Lex (· < ·) (TrainCountLex M)
          (countTrainCutoff s (M+1), s)
          (countTrainCutoff t (M+1), t))
      exact InvImage.wf (fun t : List ℕ =>
        (countTrainCutoff t (M+1), t))
        (WellFounded.prod_lex Nat.lt_wfRel.wf ih)

/-- A rank-drop certificate at a positive cutoff bounded by M
is a strict decrease of the actual well-founded relation. -/
theorem TrainCutoffRankDrop.toTrainCountLex
    (old new : List ℕ) (q : ℕ) (hq : 0 < q)
    (hDrop : TrainCutoffRankDrop old new q)
    (M : ℕ) (hBound : q ≤ M) :
    TrainCountLex M new old := by
  induction M with
  | zero => omega
  | succ M ih =>
      change Prod.Lex (· < ·) (TrainCountLex M)
        (countTrainCutoff new (M+1), new)
        (countTrainCutoff old (M+1), old)
      by_cases hHighest : q = M + 1
      · subst q
        exact Prod.Lex.left _ _ hDrop.2
      · have hLower : q ≤ M := by omega
        have hHigher : q < M + 1 := by omega
        have hSame := hDrop.1 (M+1) hHigher
        rw [hSame]
        exact Prod.Lex.right _ (ih hLower)

/-- The q>2 recursive request strictly decreases the fixed
well-founded rank, independent of inserted depth d. -/
theorem trainCutoffReplacement_wfRankDecrease
    (M q d : ℕ) (tail : List ℕ)
    (hq : 2 < q) (hBound : q ≤ M) :
    TrainCountLex M
      (List.replicate d (q - 1) ++ tail)
      (q :: tail) := by
  exact (trainCutoffReplacement_rankDrop q d tail hq).toTrainCountLex
    _ _ q (by omega) M hBound

/-- Dropping the final cutoff two is strictly rank decreasing. -/
theorem trainCutoffDropTwo_wfRankDecrease
    (M : ℕ) (tail : List ℕ) (hM : 2 ≤ M) :
    TrainCountLex M tail (2 :: tail) := by
  exact (trainCutoffDropTwo_rankDrop tail).toTrainCountLex
    _ _ 2 (by omega) M hM

end StructuralRamsey.Girth

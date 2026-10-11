import Mathlib.Tactic

/-!
# Lexicographic cutoff rank for the recursive edge-Ramsey train theorem

The circulation manuscript (Section 17) recurses on a vector of
cutoffs t = (q) ++ tail. The two recursive requests are:

  q > 2 :  (q :: tail) -> replicate d (q-1) ++ tail
  q = 2 :  (2 :: tail) -> tail.

Both strictly decrease the LEXICOGRAPHIC multiplicity vector
(c_M(t), ..., c_2(t)), even though d may be arbitrarily large.
At every cutoff strictly higher than q, counts stay unchanged;
at cutoff q, the count decreases by exactly one. The increases
in lower cutoffs do not affect lexicographic descent.

This module verifies the exact count inequalities. The actual
finite train witness induction and the use of the well-founded
lexicographic order remain separate obligations.
-/

namespace StructuralRamsey.Girth

/-- Multiplicity of a cutoff in a finite train cutoff list. -/
def countTrainCutoff (t : List ℕ) (q : ℕ) : ℕ :=
  (t.filter (fun x => decide (x = q))).length

@[simp] theorem countTrainCutoff_nil (q : ℕ) :
    countTrainCutoff [] q = 0 := by
  rfl

@[simp] theorem countTrainCutoff_cons
    (a q : ℕ) (t : List ℕ) :
    countTrainCutoff (a :: t) q =
      (if a = q then 1 else 0) + countTrainCutoff t q := by
  by_cases h : a = q
  · simp [countTrainCutoff, h]
  · simp [countTrainCutoff, h]

theorem countTrainCutoff_append
    (s t : List ℕ) (q : ℕ) :
    countTrainCutoff (s ++ t) q =
      countTrainCutoff s q + countTrainCutoff t q := by
  simp [countTrainCutoff]

theorem countTrainCutoff_replicate_ne
    (a q d : ℕ) (h : a ≠ q) :
    countTrainCutoff (List.replicate d a) q = 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [List.replicate_succ, countTrainCutoff_cons]
      simp [h, ih]

/-- A finite replacement decreases the first changed cutoff level,
independently of the number d of lower-cutoff replacements. -/
theorem trainCutoffReplacement_lowerMultiplicity
    (q d : ℕ) (tail : List ℕ) (hq : 2 < q) :
    countTrainCutoff (List.replicate d (q-1) ++ tail) q <
      countTrainCutoff (q :: tail) q := by
  have hneq : q - 1 ≠ q := by omega
  rw [countTrainCutoff_append, countTrainCutoff_replicate_ne (q-1) q d hneq]
  simp

/-- Every strictly higher level has EXACTLY the same multiplicity
before and after replacing one q by finitely many q-1 entries. -/
theorem trainCutoffReplacement_higherMultiplicity
    (q d j : ℕ) (tail : List ℕ) (hq : 2 < q) (hHigher : q < j) :
    countTrainCutoff (List.replicate d (q-1) ++ tail) j =
      countTrainCutoff (q :: tail) j := by
  have hneq : q - 1 ≠ j := by omega
  have hneq2 : q ≠ j := by omega
  rw [countTrainCutoff_append, countTrainCutoff_replicate_ne (q-1) j d hneq]
  simp [hneq2]

/-- At cutoff two, the shortened recursive target loses one level-2
member and preserves every strictly higher multiplicity. -/
theorem trainCutoffDropTwo_lowerMultiplicity
    (tail : List ℕ) :
    countTrainCutoff tail 2 < countTrainCutoff (2 :: tail) 2 := by
  simp

theorem trainCutoffDropTwo_higherMultiplicity
    (tail : List ℕ) (j : ℕ) (hHigher : 2 < j) :
    countTrainCutoff tail j = countTrainCutoff (2 :: tail) j := by
  have hneq : 2 ≠ j := by omega
  simp [hneq]

/-- An explicit certificate for a lexicographically smaller cutoff
multiplicity vector, recording its first changed coordinate. -/
def TrainCutoffRankDrop
    (old new : List ℕ) (q : ℕ) : Prop :=
  (∀ j : ℕ, q < j →
    countTrainCutoff new j = countTrainCutoff old j) ∧
  countTrainCutoff new q < countTrainCutoff old q

theorem trainCutoffReplacement_rankDrop
    (q d : ℕ) (tail : List ℕ) (hq : 2 < q) :
    TrainCutoffRankDrop (q :: tail)
      (List.replicate d (q-1) ++ tail) q := by
  constructor
  · intro j hj
    exact trainCutoffReplacement_higherMultiplicity q d j tail hq hj
  · exact trainCutoffReplacement_lowerMultiplicity q d tail hq

theorem trainCutoffDropTwo_rankDrop
    (tail : List ℕ) :
    TrainCutoffRankDrop (2 :: tail) tail 2 := by
  constructor
  · intro j hj
    exact trainCutoffDropTwo_higherMultiplicity tail j hj
  · exact trainCutoffDropTwo_lowerMultiplicity tail

end StructuralRamsey.Girth

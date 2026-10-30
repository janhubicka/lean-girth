import Girth.TrainSystemCutGirthTwo
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Globally shortest labelled cut cycles

The full circulation converse needs a *globally shortest* labelled wagon
Berge cycle, not merely a cycle whose chosen support labels happen to be
pairwise distinct. For a fixed labelled carrier family, an existing
short cycle yields a globally shortest one by Nat.find.

The important next lemma is geometric: a globally shortest labelled
cycle in a pairwise-linear family has a no-chord contact window not just
for labels occurring on the cycle, but also for arbitrary external
labels. The present module supplies the noncircular minimality input,
NOT that geometric consequence or the full system-girth theorem.
-/

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- A failed labelled cut-girth bound supplies an actual globally
minimum-length labelled Berge cycle, with length within the failed
budget. The minimization is over ALL labels and ALL physical cycles,
not only over the chosen cycle's support. -/
theorem LabelledGirthGT.exists_global_minimal_cycle_of_failure
    (carrier : I → Set V) (q : ℕ)
    (hFail : ¬ LabelledGirthGT carrier q) :
    ∃ C : LabelledBergeCycle carrier,
      C.length ≤ q ∧
      ∀ B : LabelledBergeCycle carrier, C.length ≤ B.length := by
  classical
  have hExists : ∃ C : LabelledBergeCycle carrier, C.length ≤ q := by
    exact Classical.not_not.mp hFail
  let P : ℕ → Prop :=
    fun n => ∃ C : LabelledBergeCycle carrier, C.length = n
  have hNonempty : ∃ n : ℕ, P n := by
    obtain ⟨C, _hBound⟩ := hExists
    exact ⟨C.length, C, rfl⟩
  obtain ⟨C, hC⟩ : P (Nat.find hNonempty) :=
    Nat.find_spec hNonempty
  refine ⟨C, ?_, ?_⟩
  · obtain ⟨C0, hC0⟩ := hExists
    have hMin : Nat.find hNonempty ≤ C0.length :=
      Nat.find_min' hNonempty (show P C0.length from ⟨C0, rfl⟩)
    omega
  · intro B
    have hMin : Nat.find hNonempty ≤ B.length :=
      Nat.find_min' hNonempty (show P B.length from ⟨B, rfl⟩)
    omega

/-- An independently selected globally minimal cut cycle cannot
have a strictly shorter labelled cycle. This is the direct interface
for the future chord-shortening contradiction. -/
theorem LabelledBergeCycle.no_shorter_of_global_minimal
    (carrier : I → Set V)
    (C : LabelledBergeCycle carrier)
    (hMinimal :
      ∀ B : LabelledBergeCycle carrier, C.length ≤ B.length) :
    ¬ ∃ B : LabelledBergeCycle carrier, B.length < C.length := by
  rintro ⟨B, hShort⟩
  exact (Nat.not_lt_of_ge (hMinimal B)) hShort

/-- In a pairwise-linear family, the globally shortest labelled
cycle has length at least three: a labelled length-two cycle would
give two different wagon labels sharing two distinct vertices. -/
theorem LabelledGirthGT.exists_minimal_three_of_failure
    (carrier : I → Set V) (q : ℕ)
    (hLinear : ∀ a b : I, a ≠ b →
      (carrier a ∩ carrier b).Subsingleton)
    (hFail : ¬ LabelledGirthGT carrier q) :
    ∃ C : LabelledBergeCycle carrier,
      3 ≤ C.length ∧ C.length ≤ q ∧
      ∀ B : LabelledBergeCycle carrier, C.length ≤ B.length := by
  obtain ⟨C, hBudget, hMin⟩ :=
    LabelledGirthGT.exists_global_minimal_cycle_of_failure carrier q hFail
  have hTwo : LabelledGirthGT carrier 2 :=
    labelledGirthGT_two_of_pairwiseSubsingleton carrier hLinear
  have hNotTwo : ¬ C.length ≤ 2 :=
    fun hLength => hTwo ⟨C, hLength⟩
  exact ⟨C, by omega, hBudget, hMin⟩

end StructuralRamsey.Girth

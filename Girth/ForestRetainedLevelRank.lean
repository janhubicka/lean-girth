import Girth.ForestNeutralGap
import Mathlib.Tactic

/-!
# One-shot compression of retained birth and parameter levels

Given a finite set L of retained target event levels, the compressed
coordinate of a retained level n is the number of elements of L below
n. This is strictly increasing on L and less than |L|.

More importantly, if every ancestral parameter of a retained active
code points to an earlier retained level, all those parameters can
be re-indexed to the shorter base coordinate using this rank map.
This is an exact finite syntax operation, independent of the target
history's raw depth.

It does not prove that raw partite/train histories possess a bounded
retained dependency closure, or that the compressed code can be
embedded back by an actual globally compatible free-ancestral shape
map. The meet-gap lemma addresses part of that latter task.
-/

namespace StructuralRamsey.Girth

open SuccessorTree.FreeAncestral

/-- Rank of a target level among the finitely many retained levels. -/
def retainedLevelRankCount (L : Finset ℕ) (n : ℕ) : ℕ :=
  (L.filter (fun k => k < n)).card

/-- The rank of a retained level is strictly smaller than the number
of retained levels. -/
theorem retainedLevelRankCount_lt_card
    (L : Finset ℕ) (n : ℕ) (hn : n ∈ L) :
    retainedLevelRankCount L n < L.card := by
  unfold retainedLevelRankCount
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro hEq
  have hBad : n ∈ L.filter (fun k => k < n) := by
    rw [hEq]
    exact hn
  exact (Nat.lt_irrefl n) (Finset.mem_filter.mp hBad).2

/-- Earlier retained levels receive strictly smaller ranks; no
injectivity of the original time labels beyond strict order is needed. -/
theorem retainedLevelRankCount_strict
    (L : Finset ℕ) (m n : ℕ)
    (hm : m ∈ L) (hn : n ∈ L) (hmn : m < n) :
    retainedLevelRankCount L m < retainedLevelRankCount L n := by
  unfold retainedLevelRankCount
  have hSub :
      L.filter (fun k => k < m) ⊆ L.filter (fun k => k < n) := by
    intro k hk
    obtain ⟨hkL, hkm⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨hkL, lt_trans hkm hmn⟩
  have hWitness : m ∈ L.filter (fun k => k < n) :=
    Finset.mem_filter.mpr ⟨hm, hmn⟩
  have hNot : m ∉ L.filter (fun k => k < m) := by
    simp
  have hProper :
      L.filter (fun k => k < m) ⊂ L.filter (fun k => k < n) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hSub, ?_⟩
    intro hEq
    apply hNot
    rw [hEq]
    exact hWitness
  exact Finset.card_lt_card hProper

/-- Genuine finite compressed index for each retained target level. -/
def retainedLevelRank (L : Finset ℕ) (n : {n : ℕ // n ∈ L}) :
    Fin L.card :=
  ⟨retainedLevelRankCount L n.1,
    retainedLevelRankCount_lt_card L n.1 n.2⟩

/-- The retained-level rank is an order embedding into the finite
compressed height. -/
theorem retainedLevelRank_strictMono
    (L : Finset ℕ) :
    StrictMono (retainedLevelRank L) := by
  intro m n hmn
  change retainedLevelRankCount L m.1 <
    retainedLevelRankCount L n.1
  exact retainedLevelRankCount_strict L m.1 n.1
    m.2 n.2 hmn

/-- A parameter of an active event is an earlier retained target
level. Its compressed rank is therefore a valid ancestor level
below the compressed base of the active event. -/
def compressRetainedParamTuple
    {arity n : ℕ}
    (L : Finset ℕ) (hn : n ∈ L)
    (p : ParamTuple arity n)
    (hParams : ∀ j : Fin p.len.val, (p.value j).val ∈ L) :
    ParamTuple arity (retainedLevelRankCount L n) where
  len := p.len
  value := fun j =>
    ⟨retainedLevelRankCount L (p.value j).val,
      retainedLevelRankCount_strict L
        (p.value j).val n (hParams j) hn (p.value j).isLt⟩

/-- Any retained active successor code with only earlier retained
ancestor parameters has an explicit legal compressed successor code. -/
def compressRetainedCode {Label : Type*}
    {arity n : ℕ}
    (L : Finset ℕ) (hn : n ∈ L)
    (c : Code Label arity n)
    (hParams : ∀ j : Fin c.params.len.val,
      (c.params.value j).val ∈ L) :
    Code Label arity (retainedLevelRankCount L n) where
  label := c.label
  params := compressRetainedParamTuple L hn c.params hParams

end StructuralRamsey.Girth

import Girth.TrainCyclicOwnerRuns

/-!
# Circulation: exhaustive four-way case split at real cyclic owner cuts

At each cut of a geometric owner word the neighbouring labels have
distinct owners. As their owner type is the disjoint sum of standard
indices and witness-core edge labels, there are exactly four cases:
two different standards, standard/core, core/standard, and two
different core edges. These are the precise four interfaces verified
separately for actual vertex and wagon boundary geometry.

This small theorem prevents the later witness-reduct assembly from
silently overlooking one orientation or treating same-standard
adjacency as a segment boundary. It asserts NO geometry, legal
BigCycle reduct, acceptability or appendix theorem.
-/

namespace StructuralRamsey.Girth

universe v

/-- Every actual cyclic OWNER CHANGE falls into exactly one of the
four geometrically meaningful neighbour types, with inequality of
the two labels when they lie in the same sum summand. -/
theorem cyclicOwnerCut_four_cases
    {I Core : Type v} {n : ℕ}
    (owner : Fin n → I ⊕ Core) (k : Fin n)
    (hCut : owner k ≠ owner (cyclicSucc k)) :
    (∃ i j : I, i ≠ j ∧
      owner k = Sum.inl i ∧ owner (cyclicSucc k) = Sum.inl j) ∨
    (∃ (i : I) (b : Core),
      owner k = Sum.inl i ∧ owner (cyclicSucc k) = Sum.inr b) ∨
    (∃ (b : Core) (i : I),
      owner k = Sum.inr b ∧ owner (cyclicSucc k) = Sum.inl i) ∨
    (∃ b c : Core, b ≠ c ∧
      owner k = Sum.inr b ∧ owner (cyclicSucc k) = Sum.inr c) := by
  cases hLeft : owner k with
  | inl i =>
      cases hRight : owner (cyclicSucc k) with
      | inl j =>
          have hij : i ≠ j := by
            intro hEq
            subst j
            exact hCut (hLeft.trans hRight.symm)
          exact Or.inl ⟨i, j, hij, rfl, rfl⟩
      | inr b =>
          exact Or.inr (Or.inl ⟨i, b, rfl, rfl⟩)
  | inr b =>
      cases hRight : owner (cyclicSucc k) with
      | inl i =>
          exact Or.inr (Or.inr (Or.inl ⟨b, i, rfl, rfl⟩))
      | inr c =>
          have hbc : b ≠ c := by
            intro hEq
            subst c
            exact hCut (hLeft.trans hRight.symm)
          exact Or.inr (Or.inr (Or.inr ⟨b, c, hbc, rfl, rfl⟩))

/-- Membership in the genuine finite cut set yields the exhaustive
boundary-type split, with no extra owner-distinctness hypothesis. -/
theorem cyclicOwnerCut_four_cases_of_mem
    {I Core : Type v} {n : ℕ}
    (owner : Fin n → I ⊕ Core) (k : Fin n)
    (hCut : k ∈ cyclicOwnerCutPositions owner) :
    (∃ i j : I, i ≠ j ∧
      owner k = Sum.inl i ∧ owner (cyclicSucc k) = Sum.inl j) ∨
    (∃ (i : I) (b : Core),
      owner k = Sum.inl i ∧ owner (cyclicSucc k) = Sum.inr b) ∨
    (∃ (b : Core) (i : I),
      owner k = Sum.inr b ∧ owner (cyclicSucc k) = Sum.inl i) ∨
    (∃ b c : Core, b ≠ c ∧
      owner k = Sum.inr b ∧ owner (cyclicSucc k) = Sum.inr c) :=
  cyclicOwnerCut_four_cases owner k
    ((mem_cyclicOwnerCutPositions_iff owner k).mp hCut)

end StructuralRamsey.Girth

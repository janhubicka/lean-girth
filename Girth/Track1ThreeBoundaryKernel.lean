import Girth.Berge
import Mathlib.Tactic

/-!
# Three narrow boundaries force a join-tree middle

This is the finite set argument required by the cutoff-three construction.
The actual partite-picture geometry is not assumed or proved here.

DRAFT / NOT KERNEL-CHECKED: no local Lean installation is available in
this run. Do not use this source as a validation certificate until an
exact-head Lean build and #print axioms check have succeeded.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- For three boundaries each empty, singleton or a genuine edge,
girth > 3 forces some boundary to contain the intersection of
the other two. This is independent of the partite attachment. -/
theorem three_boundary_middle_of_girthGT_three
    (H : Set (Set W)) (hGirth : GirthGT H 3)
    (S₀ S₁ S₂ : Set W)
    (h₀ : S₀.Subsingleton ∨ S₀ ∈ H)
    (h₁ : S₁.Subsingleton ∨ S₁ ∈ H)
    (h₂ : S₂.Subsingleton ∨ S₂ ∈ H) :
    (S₁ ∩ S₂ ⊆ S₀) ∨ (S₀ ∩ S₂ ⊆ S₁) ∨ (S₀ ∩ S₁ ⊆ S₂) := by
  classical
  by_contra hn
  have hn₀ : ¬ (S₁ ∩ S₂ ⊆ S₀) := fun h => hn (Or.inl h)
  have hn₁ : ¬ (S₀ ∩ S₂ ⊆ S₁) := fun h => hn (Or.inr (Or.inl h))
  have hn₂ : ¬ (S₀ ∩ S₁ ⊆ S₂) := fun h => hn (Or.inr (Or.inr h))
  obtain ⟨x₀, hx₀, hx₀n⟩ := Set.not_subset.mp hn₀
  obtain ⟨x₁, hx₁, hx₁n⟩ := Set.not_subset.mp hn₁
  obtain ⟨x₂, hx₂, hx₂n⟩ := Set.not_subset.mp hn₂
  have hx₀₁ : x₀ ∈ S₁ := hx₀.1
  have hx₀₂ : x₀ ∈ S₂ := hx₀.2
  have hx₁₀ : x₁ ∈ S₀ := hx₁.1
  have hx₁₂ : x₁ ∈ S₂ := hx₁.2
  have hx₂₀ : x₂ ∈ S₀ := hx₂.1
  have hx₂₁ : x₂ ∈ S₁ := hx₂.2
  have hne₀₁ : x₀ ≠ x₁ := by
    intro h
    apply hx₀n
    rw [h]
    exact hx₁₀
  have hne₀₂ : x₀ ≠ x₂ := by
    intro h
    apply hx₀n
    rw [h]
    exact hx₂₀
  have hne₁₂ : x₁ ≠ x₂ := by
    intro h
    apply hx₁n
    rw [h]
    exact hx₂₁
  have he₀ : S₀ ∈ H := by
    rcases h₀ with hsmall | hedge
    · exact (hne₁₂ (hsmall hx₁₀ hx₂₀)).elim
    · exact hedge
  have he₁ : S₁ ∈ H := by
    rcases h₁ with hsmall | hedge
    · exact (hne₀₂ (hsmall hx₀₁ hx₂₁)).elim
    · exact hedge
  have he₂ : S₂ ∈ H := by
    rcases h₂ with hsmall | hedge
    · exact (hne₀₁ (hsmall hx₀₂ hx₁₂)).elim
    · exact hedge
  have hed₀₁ : S₀ ≠ S₁ := by
    intro h
    apply hx₀n
    rw [h]
    exact hx₀₁
  have hed₀₂ : S₀ ≠ S₂ := by
    intro h
    apply hx₀n
    rw [h]
    exact hx₀₂
  have hed₁₂ : S₁ ≠ S₂ := by
    intro h
    apply hx₁n
    rw [h]
    exact hx₁₂
  have hed₁₀ : S₁ ≠ S₀ := Ne.symm hed₀₁
  have hed₂₀ : S₂ ≠ S₀ := Ne.symm hed₀₂
  have hed₂₁ : S₂ ≠ S₁ := Ne.symm hed₁₂
  have hne₁₀ : x₁ ≠ x₀ := Ne.symm hne₀₁
  have hne₂₀ : x₂ ≠ x₀ := Ne.symm hne₀₂
  have hne₂₁ : x₂ ≠ x₁ := Ne.symm hne₁₂
  let c : BergeCycle H := {
    length := 3
    hlength := by omega
    edge := ![S₀, S₁, S₂]
    vertex := ![x₂, x₀, x₁]
    edge_mem := by
      intro i
      fin_cases i
      · exact he₀
      · exact he₁
      · exact he₂
    edge_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    vertex_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    left_mem := by
      intro i
      fin_cases i
      · exact hx₂₀
      · exact hx₀₁
      · exact hx₁₂
    right_mem := by
      intro i
      fin_cases i
      · simpa [cyclicSucc] using hx₂₁
      · simpa [cyclicSucc] using hx₀₂
      · simpa [cyclicSucc] using hx₁₀
  }
  exact hGirth ⟨c, by decide⟩

#print axioms StructuralRamsey.Girth.three_boundary_middle_of_girthGT_three

end StructuralRamsey.Girth

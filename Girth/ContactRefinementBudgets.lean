import Girth.ContactRefinedStripInput

/-! Numerical budgets and part parameters of an actual strip
refinement, independent of the existence of forest-boosted witnesses. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B : Type v} {h : ℕ}
variable {D : ContactHypergraphData V E I} {base : B → Set X}

namespace ContactBaseProjection.StripRefinement
variable {P : ContactBaseProjection D base} {T : ContactTrainData E (h+1)}
variable {allowed : Fin (h+1) → Set X} {g : ℕ} {b : B}
variable (R : P.StripRefinement T allowed g b)

/-- Restrict the ambient allowed sets to the actual part type of
this strip. The first d entries are singleton or empty. -/
def boostAllowed (j : Fin (R.depth+h)) : Set (base b) :=
  Subtype.val ⁻¹' R.allAllowed j

/-- The class-wide forest boost aims at the original bottom budget.
Its positive bounds, and hence the recursive rank, are precisely
those of the refined tail. -/
def boostBounds (q : Fin (h+2) → ℕ) (μ : Fin (R.depth+h+1)) : ℕ :=
  if μ.val = 0 then q 0 else R.allBounds q μ

theorem boostBounds_zero (q : Fin (h+2) → ℕ) : R.boostBounds q 0 = q 0 := by
  simp [boostBounds]

theorem boostBounds_two (q : Fin (h+2) → ℕ) (hg : 2 ≤ g)
    (hq : ∀ μ, μ.val < h+1 → 2 ≤ q μ) :
    ∀ μ, μ.val < R.depth+h → 2 ≤ R.boostBounds q μ := by
  intro μ hproper
  have hval := μ.isLt
  by_cases hz : μ.val = 0
  · rw [boostBounds,if_pos hz]
    exact hq 0 (by change (0 : ℕ) < h+1; omega)
  · rw [boostBounds,if_neg hz]
    by_cases hp : μ.val < R.depth
    · simpa only [allBounds,if_pos hp] using hg
    · let k : Fin (h+2) := ⟨μ.val-R.depth+1,by have := μ.isLt; omega⟩
      have hk : k.val < h+1 := by change μ.val-R.depth+1 < h+1; omega
      simpa only [allBounds,if_neg hp] using hq k hk

end ContactBaseProjection.StripRefinement
end StructuralRamsey.Girth

import Girth.ForestReplayObstruction

/-!
# A safe geometric union criterion over a pair-closed common vertex set

Although the universal private multi-contact replay construction is false,
ordinary linear support *is* closed under free unions when the shared part
is pair-closed: no genuinely new edge is allowed to contain two old
vertices. This is the basic local operation for a replacement reservoir.

The theorem is intentionally a criterion on already embedded edge sets.
Constructing the global pointed B-copy evaluation and maintaining its
pairwise-clean named copies remains separate work.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- If every cross-intersection of an E1-edge and an E2-edge lies in the
old shared vertex set V0, and each E1-edge meeting V0 twice is already
an E2-edge, then the union of the two linear edge sets is linear.

In a free amalgam over a pair-closed base, cross intersections lie in
the base and every edge touching the base in two points belongs to the
common support. -/
theorem linearEdgeSet_union_of_pairClosedOverlap
    (E₁ E₂ : Set (Set W)) (V₀ : Set W)
    (hLinear₁ : LinearEdgeSet E₁)
    (hLinear₂ : LinearEdgeSet E₂)
    (hCross :
      ∀ ⦃e f : Set W⦄, e ∈ E₁ → f ∈ E₂ → e ∩ f ⊆ V₀)
    (hPairClosed :
      ∀ ⦃e : Set W⦄, e ∈ E₁ →
        ¬ (e ∩ V₀).Subsingleton → e ∈ E₂) :
    LinearEdgeSet (E₁ ∪ E₂) := by
  intro e f he hf hef
  rcases he with he₁ | he₂
  · rcases hf with hf₁ | hf₂
    · exact hLinear₁ he₁ hf₁ hef
    · by_cases hSmall : (e ∩ V₀).Subsingleton
      · intro x hx y hy
        apply hSmall
        · exact ⟨hx.1, hCross he₁ hf₂ hx⟩
        · exact ⟨hy.1, hCross he₁ hf₂ hy⟩
      · exact hLinear₂ (hPairClosed he₁ hSmall) hf₂ hef
  · rcases hf with hf₁ | hf₂
    · have hSmallFE : (f ∩ e).Subsingleton := by
        by_cases hSmall : (f ∩ V₀).Subsingleton
        · intro x hx y hy
          apply hSmall
          · exact ⟨hx.1, hCross hf₁ he₂ hx⟩
          · exact ⟨hy.1, hCross hf₁ he₂ hy⟩
        · exact hLinear₂ (hPairClosed hf₁ hSmall) he₂ hef.symm
      simpa [Set.inter_comm] using hSmallFE
    · exact hLinear₂ he₂ hf₂ hef

end StructuralRamsey.Girth

import Girth.Berge
import Girth.ForestCarrierCorner
import Mathlib.Tactic

/-!
# A-linearity is precisely the absence of length-two Berge cycles

The circulation proof preserves A-linearity in its standard picture
attachment.  The generic forest-completion assembly is phrased using
ambient support girth greater than two.  This small bridge shows those
hypotheses are equivalent; no higher-girth assumption or ambient
finiteness is required.

The direction from girth to linearity already appears in Girth.Berge.
-/

namespace StructuralRamsey.Girth

universe u v

/-- An edge family with pairwise subsingleton intersections has no
Berge cycle of length at most two. The converse is
pairwise_subsingleton_of_girthGT_two. -/
theorem girthGT_two_of_linearEdgeSet
    {W : Type v} {H : Set (Set W)}
    (hLinear : LinearEdgeSet H) :
    GirthGT H 2 := by
  rintro ⟨c, hLength⟩
  have hcLength : c.length = 2 := by
    have hpos := c.hlength
    omega
  let i₀ : Fin c.length := ⟨0, by omega⟩
  let i₁ : Fin c.length := ⟨1, by omega⟩
  have hDistinctEdges : c.edge i₀ ≠ c.edge i₁ := by
    intro hEq
    have hIndices := c.edge_injective hEq
    have hValues := congrArg Fin.val hIndices
    change (0 : ℕ) = 1 at hValues
    omega
  have hNext₀ : cyclicSucc i₀ = i₁ := by
    apply Fin.ext
    change (0 + 1) % c.length = 1
    rw [hcLength]
  have hNext₁ : cyclicSucc i₁ = i₀ := by
    apply Fin.ext
    change (1 + 1) % c.length = 0
    rw [hcLength]
  have hAt₀ : c.vertex i₀ ∈ c.edge i₀ ∩ c.edge i₁ := by
    constructor
    · exact c.left_mem i₀
    · simpa only [hNext₀] using c.right_mem i₀
  have hAt₁ : c.vertex i₁ ∈ c.edge i₀ ∩ c.edge i₁ := by
    constructor
    · simpa only [hNext₁] using c.right_mem i₁
    · exact c.left_mem i₁
  have hSmall : (c.edge i₀ ∩ c.edge i₁).Subsingleton :=
    hLinear (c.edge_mem i₀) (c.edge_mem i₁) hDistinctEdges
  have hEqVertices := hSmall hAt₀ hAt₁
  have hIndices := c.vertex_injective hEqVertices
  have hValues := congrArg Fin.val hIndices
  change (0 : ℕ) = 1 at hValues
  omega

/-- The picture-step invariant ALinear gives exactly the ambient
girth-two hypothesis needed by the forest-completion assembly. -/
theorem girthGT_two_of_aLinear
    {L : RelLanguage.{u}} {UA W : Type v}
    (A : StructuralRamsey.RelStructure L UA)
    (D : StructuralRamsey.RelStructure L W)
    (hLinear : ALinear A D) :
    GirthGT (supportCopies A D) 2 := by
  apply girthGT_two_of_linearEdgeSet
  intro E F hE hF hEF
  obtain ⟨a, rfl⟩ := hE
  obtain ⟨b, rfl⟩ := hF
  exact hLinear a b hEF

end StructuralRamsey.Girth

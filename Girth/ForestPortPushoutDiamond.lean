import Girth.ForestPortPushoutActualUnion
import Mathlib.Tactic

/-!
# Order independence of two independent B-leaf port attachments

The first compositional adversarial test for a bounded alternative
B-forest history has three pieces: one old middle piece and two
independent leaf attachments.

On vertex sets U,V,T of one actual ambient host, one may glue
the leaf V first and T second, or glue T first and V second.
The canonical one-step pushout equivalences show that both
syntactic vertex types represent the SAME physical union.

This is a two-leaf diamond theorem for finite geometric
presentations. It is NOT yet naturality of the successor-tree
shape action on intrinsic carrier labels or proof that all
three-piece histories occur cofinally in a Ramsey host.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

namespace PortGluing

/-- The two possible parenthesizations/orderings of a base with
two leaf vertex sets have an exact underlying union equivalence. -/
def swapTwoLeafUnionSubtype
    (U V T : Set W) :
    {w : W // w ∈ (U ∪ V) ∪ T} ≃
      {w : W // w ∈ (U ∪ T) ∪ V} where
  toFun := fun x => ⟨x.1, by
    rcases x.2 with hUV | hT
    · rcases hUV with hU | hV
      · exact Or.inl (Or.inl hU)
      · exact Or.inr hV
    · exact Or.inl (Or.inr hT)⟩
  invFun := fun x => ⟨x.1, by
    rcases x.2 with hUT | hV
    · rcases hUT with hU | hT
      · exact Or.inl (Or.inl hU)
      · exact Or.inr hT
    · exact Or.inl (Or.inr hV)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl

/-- Canonical commutation of TWO one-leaf vertex pushouts. Both
directions are built through their actual ambient vertex union,
not by separately guessed per-copy transports. -/
noncomputable def twoLeafPushoutOrderEquiv
    (U V T : Set W) :
    (ofIntersectingSets (U ∪ V) T).Vertex ≃
      (ofIntersectingSets (U ∪ T) V).Vertex :=
  ((overlapToUnionEquiv (U ∪ V) T).trans
    (swapTwoLeafUnionSubtype U V T)).trans
      (overlapToUnionEquiv (U ∪ T) V).symm

/-- On the actual ambient host, swapping the order of two independent
leaf births cannot move any physical vertex: the intermediate union
equivalence is the identity on the underlying W coordinate. -/
theorem swapTwoLeafUnionSubtype_val
    (U V T : Set W)
    (x : {w : W // w ∈ (U ∪ V) ∪ T}) :
    (swapTwoLeafUnionSubtype U V T x).1 = x.1 := rfl

end PortGluing

end StructuralRamsey.Girth

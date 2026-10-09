import Girth.ForestPortPushoutUniversal
import Mathlib.Tactic

/-!
# Every two-subset union is the canonical port pushout of its intersection

For two vertex sets U,V in a common ambient universe W, form the
canonical port gluing with old type U, new type V, and the shared
port equal to the overlap U∩V, identified by equal ambient vertices.

The resulting canonical glued vertex type is actually EQUIVALENT
to U∪V, even if the sets or ambient universe are infinite. This is
the concrete one-step reconstruction needed for the canonical
leaf-birth presentation of a finite supported B-forest.

The support-edge union is handled separately; the result does
not assert ambient relational A-copy ownership or successor-history
shape-map compatibility.
-/

namespace StructuralRamsey.Girth

universe v

namespace PortGluing

variable {W : Type v}

/-- The exact port identification for two subsets of one host,
with the same ambient vertex represented by a subtype on each side. -/
def ofIntersectingSets (U V : Set W) : PortGluing U V where
  oldPort := {x : U | x.1 ∈ V}
  newPort := {y : V | y.1 ∈ U}
  identify :=
    { toFun := fun y =>
        ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      invFun := fun x =>
        ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      left_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        rfl }

/-- The physical map from the explicit pushout of the two subsets
into their actual ambient union. -/
def overlapToUnion (U V : Set W) :
    (ofIntersectingSets U V).Vertex → {w : W // w ∈ U ∪ V}
  | .inl x => ⟨x.1, Or.inl x.2⟩
  | .inr y => ⟨y.1.1, Or.inr y.1.2⟩

/-- The new private vertices really are outside the old subset,
so the two physical summands cannot be accidentally identified. -/
theorem overlapToUnion_injective (U V : Set W) :
    Function.Injective (overlapToUnion U V) := by
  intro a b hab
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          have hval : x.1 = y.1 :=
            congrArg Subtype.val hab
          exact congrArg Sum.inl (Subtype.ext hval)
      | inr y =>
          exfalso
          have hval : x.1 = y.1.1 :=
            congrArg Subtype.val hab
          have hyNot : y.1.1 ∉ U := y.2
          exact hyNot (by simpa only [← hval] using x.2)
  | inr x =>
      cases b with
      | inl y =>
          exfalso
          have hval : x.1.1 = y.1 :=
            congrArg Subtype.val hab
          have hxNot : x.1.1 ∉ U := x.2
          exact hxNot (by simpa only [hval] using y.2)
      | inr y =>
          have hval : x.1.1 = y.1.1 :=
            congrArg Subtype.val hab
          have hxy : x = y := by
            apply Subtype.ext
            apply Subtype.ext
            exact hval
          exact congrArg Sum.inr hxy

/-- Every vertex of the actual union has a representative in the
canonical glued picture. -/
theorem overlapToUnion_surjective (U V : Set W) :
    Function.Surjective (overlapToUnion U V) := by
  rintro ⟨w, hw⟩
  rcases hw with hU | hV
  · exact ⟨Sum.inl ⟨w, hU⟩, rfl⟩
  · by_cases hU : w ∈ U
    · exact ⟨Sum.inl ⟨w, hU⟩, rfl⟩
    · refine ⟨Sum.inr ⟨⟨w, hV⟩, ?_⟩, rfl⟩
      exact hU

/-- Canonical vertex equivalence between one-step gluing and the
physical old-plus-new union. No choice, finiteness or cardinality
argument is necessary. -/
noncomputable def overlapToUnionEquiv (U V : Set W) :
    (ofIntersectingSets U V).Vertex ≃ {w : W // w ∈ U ∪ V} :=
  Equiv.ofBijective (overlapToUnion U V)
    ⟨overlapToUnion_injective U V,
      overlapToUnion_surjective U V⟩

end PortGluing

end StructuralRamsey.Girth

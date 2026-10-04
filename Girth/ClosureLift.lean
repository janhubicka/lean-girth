import Girth.ClosureExpansion

/-! # Lifting A-copies to the target closure expansion

Every relational embedding A -> B lifts to a full embedding between the
corresponding c_A/c_B target expansions when B is A-linear.  This is the
internal closure step used when translating the Ramsey arrow back to the
relational language.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}

/-- A relational A-copy in an A-linear B is automatically a full embedding of
the target closure expansions. -/
def targetClosureLift
    {A : RelStructure L U} {B : RelStructure L V}
    (hLinear : ALinear A B)
    (a : RelStructure.Embedding A B) :
    StructuralRamsey.Structure.Embedding
      (targetClosureExpansion A A)
      (targetClosureExpansion A B) where
  toFun := a
  injective := a.injective
  map_rel_iff R x := by
    exact a.map_rel_iff R x
  map_func := by
    intro F x
    cases F with
    | cA =>
        simp only [closureLanguage] at x
        change
          StructuralRamsey.Structure.imageSet a (cAValue A A x) =
            cAValue A B (a ∘ x)
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          rcases hz with ⟨hxy, s, hx, hy, hz⟩
          have hxy' : a (x 0) ≠ a (x 1) := by
            intro heq
            exact hxy (a.injective heq)
          refine ⟨hxy', a.comp s, ?_, ?_, ?_⟩
          · rcases hx with ⟨t, ht⟩
            exact ⟨t, congrArg a ht⟩
          · rcases hy with ⟨t, ht⟩
            exact ⟨t, congrArg a ht⟩
          · rcases hz with ⟨t, ht⟩
            exact ⟨t, congrArg a ht⟩
        · intro hy
          rcases hy with ⟨hxy, b, h0b, h1b, hyb⟩
          have hxySrc : x 0 ≠ x 1 := by
            intro heq
            apply hxy
            exact congrArg a heq
          have h0a : a (x 0) ∈ copyCarrier a :=
            ⟨x 0, rfl⟩
          have h1a : a (x 1) ∈ copyCarrier a :=
            ⟨x 1, rfl⟩
          have hsame : SameCopy b a :=
            sameCopy_of_common_distinct_pair hLinear b a
              h0b h1b h0a h1a hxy
          have hya : y ∈ copyCarrier a := by
            change copyCarrier b = copyCarrier a at hsame
            rw [← hsame]
            exact hyb
          rcases hya with ⟨z, hz⟩
          refine ⟨z, ?_, hz⟩
          refine ⟨hxySrc, RelStructure.Embedding.id A, ?_, ?_, ?_⟩
          · exact ⟨x 0, rfl⟩
          · exact ⟨x 1, rfl⟩
          · exact ⟨z, rfl⟩
    | cB =>
        simp only [closureLanguage] at x
        change
          StructuralRamsey.Structure.imageSet a (cBValue A A x) =
            cBValue A B (a ∘ x)
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          rcases hz with ⟨_, hno⟩
          exfalso
          apply hno
          refine ⟨RelStructure.Embedding.id A, ?_, ?_, ?_⟩
          · exact ⟨x 0, rfl⟩
          · exact ⟨x 1, rfl⟩
          · exact ⟨x 2, rfl⟩
        · intro hy
          rcases hy with ⟨_, hno⟩
          exfalso
          apply hno
          refine ⟨a, ?_, ?_, ?_⟩
          · exact ⟨x 0, rfl⟩
          · exact ⟨x 1, rfl⟩
          · exact ⟨x 2, rfl⟩

@[simp]
theorem targetClosureLift_apply
    {A : RelStructure L U} {B : RelStructure L V}
    (hLinear : ALinear A B)
    (a : RelStructure.Embedding A B)
    (x : U) :
    targetClosureLift hLinear a x = a x :=
  rfl

end StructuralRamsey.Girth

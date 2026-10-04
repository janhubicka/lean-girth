import Girth.ClosureExpansion
import Girth.TreeGeometry

/-! # Elementary closure embeddings and free-amalgam sides

This module develops the reusable pieces needed to show that elementary
A-closure expansions form a free-amalgamation class.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U D E F C : Type v}

/-- An induced relational embedding with A-strong image lifts to a full
embedding of the elementary c_A closure expansions. -/
def elementaryClosureEmbeddingOfStrong
    {A : RelStructure L U} {D₀ : RelStructure L D}
    {E₀ : RelStructure L E}
    (e : RelStructure.Embedding D₀ E₀)
    (hStrong : AStrong A E₀ (copyCarrier e)) :
    StructuralRamsey.Structure.Embedding
      (elementaryClosureExpansion A D₀)
      (elementaryClosureExpansion A E₀) where
  toFun := e
  injective := e.injective
  map_rel_iff R x := e.map_rel_iff R x
  map_func := by
    intro Fsym x
    cases Fsym with
    | cB =>
        simp only [closureLanguage] at x
        simp [elementaryClosureExpansion,
          StructuralRamsey.Structure.imageSet]
    | cA =>
        simp only [closureLanguage] at x
        change
          StructuralRamsey.Structure.imageSet e (cAValue A D₀ x) =
            cAValue A E₀ (e ∘ x)
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          rcases hz with ⟨hxy, a, h0, h1, hz⟩
          have hxy' : e (x 0) ≠ e (x 1) := by
            intro heq
            exact hxy (e.injective heq)
          refine ⟨hxy', e.comp a, ?_, ?_, ?_⟩
          · rcases h0 with ⟨t, ht⟩
            exact ⟨t, congrArg e ht⟩
          · rcases h1 with ⟨t, ht⟩
            exact ⟨t, congrArg e ht⟩
          · rcases hz with ⟨t, ht⟩
            exact ⟨t, congrArg e ht⟩
        · intro hy
          rcases hy with ⟨hxy, b, h0, h1, hyb⟩
          have hMeet :
              ¬ (copyCarrier b ∩ copyCarrier e).Subsingleton := by
            intro hs
            exact hxy (hs
              ⟨h0, ⟨x 0, rfl⟩⟩
              ⟨h1, ⟨x 1, rfl⟩⟩)
          have hbSub : copyCarrier b ⊆ copyCarrier e :=
            hStrong b hMeet
          have hfactor : ∀ a : U, ∃ d : D, b a = e d := by
            intro a
            rcases hbSub ⟨a, rfl⟩ with ⟨d, hd⟩
            exact ⟨d, hd.symm⟩
          let bD : RelStructure.Embedding A D₀ :=
            b.factorThroughRange e hfactor
          have hbD (a : U) : b a = e (bD a) :=
            Classical.choose_spec (hfactor a)
          have hxySrc : x 0 ≠ x 1 := by
            intro heq
            apply hxy
            exact congrArg e heq
          have h0D : x 0 ∈ copyCarrier bD := by
            rcases h0 with ⟨a0, ha0⟩
            refine ⟨a0, ?_⟩
            apply e.injective
            calc
              e (bD a0) = b a0 := (hbD a0).symm
              _ = e (x 0) := ha0
          have h1D : x 1 ∈ copyCarrier bD := by
            rcases h1 with ⟨a1, ha1⟩
            refine ⟨a1, ?_⟩
            apply e.injective
            calc
              e (bD a1) = b a1 := (hbD a1).symm
              _ = e (x 1) := ha1
          have hyE : y ∈ copyCarrier e := hbSub hyb
          rcases hyE with ⟨z, hz⟩
          refine ⟨z, ?_, hz⟩
          have hzD : z ∈ copyCarrier bD := by
            rcases hyb with ⟨az, haz⟩
            refine ⟨az, ?_⟩
            apply e.injective
            calc
              e (bD az) = b az := (hbD az).symm
              _ = y := haz
              _ = e z := hz.symm
          exact ⟨hxySrc, bD, h0D, h1D, hzD⟩

@[simp]
theorem elementaryClosureEmbeddingOfStrong_apply
    {A : RelStructure L U} {D₀ : RelStructure L D}
    {E₀ : RelStructure L E}
    (e : RelStructure.Embedding D₀ E₀)
    (hStrong : AStrong A E₀ (copyCarrier e))
    (x : D) :
    elementaryClosureEmbeddingOfStrong e hStrong x = e x :=
  rfl

end StructuralRamsey.Girth

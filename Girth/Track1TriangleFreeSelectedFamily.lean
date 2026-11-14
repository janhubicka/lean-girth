import Girth.Track1TriangleFreeEHNClass
import Girth.ALinearRamsey
import PartiteConstruction.Structure.Order

/-!
# Track 1: actual ordered selected target family in girth >3 EHN class

This is the stronger fresh-order-respecting selected-family interface of
Track1OrderedSelectedFamily, instantiated with the new canonical c_A
triangle-free EHN class. The ternary c_B is arbitrary in the class,
and the fresh EHN order is preserved by every selected embedding.

This does not construct the final owner-split coloured witness or the
partite fusion. DRAFT / NOT KERNEL-CHECKED.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {U V : Type v}

/-- The full fresh-ordered target embeddings form a canonical *selected*
relational B family, and the Ramsey arrow can be witnessed inside it. -/
theorem track1_selectedOrderedRamseyFamily_triangleFree
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hAirr : A.Irreducible)
    (hBlin : ALinear A B)
    (hBgirth : GirthGT (supportCopies A B) 3)
    (hmono : ∀ a : RelStructure.Embedding A B, StrictMono a)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : StructuralRamsey.Structure (closureLanguage L) W)
      (family : Set (RelStructure.Embedding B (closureRelReduct C))),
      ElementaryCAThreeClass A C ∧
      (∀ b, b ∈ family →
        ∀ x y : V, x < y → @LT.lt W o.toLT (b x) (b y)) ∧
      (∀ b, b ∈ family →
        AStrong A (closureRelReduct C) (copyCarrier b)) ∧
      (∀ b, b ∈ family → ∀ c, c ∈ family →
        ¬ SameCopy b c →
        (copyCarrier b ∩ copyCarrier c).Subsingleton ∨
          ∃ a : RelStructure.Embedding A (closureRelReduct C),
            copyCarrier b ∩ copyCarrier c = copyCarrier a) ∧
      (∀ χ : RelStructure.Embedding A (closureRelReduct C) → κ,
        ∃ b, b ∈ family ∧
          ∀ a₁ a₂ : RelStructure.Embedding A B,
            χ (b.comp a₁) = χ (b.comp a₂)) := by
  classical
  let K : StructuralRamsey.Structure.StructureClass.{u,v}
      (L := closureLanguage L) := ElementaryCAThreeClass A
  have hK : StructuralRamsey.Structure.FreeAmalgamationClass K :=
    ElementaryCAThreeClass_freeAmalgamationClass A hAirr
  let Ahat := targetClosureExpansion A A
  let Bhat := targetClosureExpansion A B
  have hBmem : K Bhat :=
    targetClosure_mem_ElementaryCAThreeClass hBlin hBgirth
  obtain ⟨W, hW, o, C, hCmem, hRamsey⟩ :=
    hK.orderedRamsey_of_mem_target
      Ahat Bhat hBmem closureLanguage_positiveFuncArity κ
  letI : Finite W := hW
  letI : LinearOrder W := o
  let family : Set (RelStructure.Embedding B (closureRelReduct C)) :=
    Set.range (fun b : StructuralRamsey.Structure.Embedding
        Bhat.withLinearOrder C.withLinearOrder =>
          targetEmbeddingRel b.linearOrderReduct)
  refine ⟨W, hW, o, C, family, hCmem, ?_, ?_, ?_, ?_⟩
  · intro b hb x y hxy
    obtain ⟨eb, rfl⟩ := hb
    change eb x < eb y
    exact (StructuralRamsey.Structure.Embedding.strictMono eb) hxy
  · intro b hb
    obtain ⟨eb, rfl⟩ := hb
    exact targetEmbedding_range_aStrong hCmem.1.2 eb.linearOrderReduct
  · intro b hb c hc hne
    obtain ⟨eb, rfl⟩ := hb
    obtain ⟨ec, rfl⟩ := hc
    exact targetEmbeddings_controlledIntersection
      hBlin eb.linearOrderReduct ec.linearOrderReduct hne
  · intro χ
    let χhat : StructuralRamsey.Structure.Embedding
        Ahat.withLinearOrder C.withLinearOrder → κ :=
      fun e => χ (targetEmbeddingRel e.linearOrderReduct)
    obtain ⟨b, hb⟩ := hRamsey χhat
    let br : RelStructure.Embedding B (closureRelReduct C) :=
      targetEmbeddingRel b.linearOrderReduct
    refine ⟨br, ⟨b, rfl⟩, ?_⟩
    intro a₁ a₂
    let a₁f : StructuralRamsey.Structure.Embedding Ahat Bhat :=
      targetClosureLift hBlin a₁
    let a₂f : StructuralRamsey.Structure.Embedding Ahat Bhat :=
      targetClosureLift hBlin a₂
    let a₁o : StructuralRamsey.Structure.Embedding
        Ahat.withLinearOrder Bhat.withLinearOrder :=
      structureEmbeddingWithLinearOrder a₁f (hmono a₁)
    let a₂o : StructuralRamsey.Structure.Embedding
        Ahat.withLinearOrder Bhat.withLinearOrder :=
      structureEmbeddingWithLinearOrder a₂f (hmono a₂)
    have hcomp₁ :
        targetEmbeddingRel ((b.comp a₁o).linearOrderReduct) =
          br.comp a₁ := by
      apply RelStructure.Embedding.ext
      intro x
      rfl
    have hcomp₂ :
        targetEmbeddingRel ((b.comp a₂o).linearOrderReduct) =
          br.comp a₂ := by
      apply RelStructure.Embedding.ext
      intro x
      rfl
    have hc := hb a₁o a₂o
    change χ (targetEmbeddingRel
      ((b.comp a₁o).linearOrderReduct)) =
        χ (targetEmbeddingRel
          ((b.comp a₂o).linearOrderReduct)) at hc
    calc
      χ (br.comp a₁) =
          χ (targetEmbeddingRel
            ((b.comp a₁o).linearOrderReduct)) :=
        congrArg χ hcomp₁.symm
      _ = χ (targetEmbeddingRel
          ((b.comp a₂o).linearOrderReduct)) := hc
      _ = χ (br.comp a₂) := congrArg χ hcomp₂

#print axioms StructuralRamsey.Girth.track1_selectedOrderedRamseyFamily_triangleFree

end StructuralRamsey.Girth

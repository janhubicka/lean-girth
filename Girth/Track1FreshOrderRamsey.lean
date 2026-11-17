import Girth.ALinearRamsey
import PartiteConstruction.Structure.Order

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {U V : Type v}

/-- The selected family can be restricted to the embeddings that preserve
the auxiliary EHN order, while retaining the relational Ramsey arrow. -/
theorem freshOrderedClosedTargetRamseyFamily_of_mem
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    {K : StructuralRamsey.Structure.StructureClass.{u,v} (L := closureLanguage L)}
    (hK : StructuralRamsey.Structure.FreeAmalgamationClass K)
    (hBmem : K (targetClosureExpansion A B))
    (hBlin : ALinear A B)
    (hMono : ∀ a : Embedding A B, StrictMono a)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : StructuralRamsey.Structure (closureLanguage L) W),
      K C ∧ ∀ χ : Embedding A (closureRelReduct C) → κ,
        ∃ b : StructuralRamsey.Structure.Embedding (targetClosureExpansion A B) C,
          (∀ x y : V, x < y → @LT.lt W o.toLT (b x) (b y)) ∧
          ∀ a c : Embedding A B,
            χ ((targetEmbeddingRel b).comp a) = χ ((targetEmbeddingRel b).comp c) := by
  classical
  let Ahat := targetClosureExpansion A A
  let Bhat := targetClosureExpansion A B
  obtain ⟨W, hW, o, C, hCmem, hRamsey⟩ :=
    hK.orderedRamsey_of_mem_target Ahat Bhat hBmem closureLanguage_positiveFuncArity κ
  letI : Finite W := hW
  letI : LinearOrder W := o
  refine ⟨W, hW, o, C, hCmem, ?_⟩
  intro χ
  let χhat : StructuralRamsey.Structure.Embedding Ahat.withLinearOrder C.withLinearOrder → κ :=
    fun e => χ (targetEmbeddingRel e.linearOrderReduct)
  obtain ⟨b, hb⟩ := hRamsey χhat
  let b₀ : StructuralRamsey.Structure.Embedding Bhat C := b.linearOrderReduct
  refine ⟨b₀, fun x y hxy => StructuralRamsey.Structure.Embedding.strictMono b hxy, ?_⟩
  intro a c
  let a₁ := structureEmbeddingWithLinearOrder (targetClosureLift hBlin a) (hMono a)
  let c₁ := structureEmbeddingWithLinearOrder (targetClosureLift hBlin c) (hMono c)
  have hComp (d : Embedding A B) (d₁ : StructuralRamsey.Structure.Embedding
      Ahat.withLinearOrder Bhat.withLinearOrder) (hMatch : ∀ u, d₁ u = d u) :
      targetEmbeddingRel ((b.comp d₁).linearOrderReduct) = (targetEmbeddingRel b₀).comp d := by
    apply Embedding.ext
    intro u
    change b (d₁ u) = b (d u)
    rw [hMatch u]
  exact ((congrArg χ (hComp a a₁ (fun _ => rfl))).symm.trans (hb a₁ c₁)).trans
    (congrArg χ (hComp c c₁ (fun _ => rfl)))

#print axioms StructuralRamsey.Girth.freshOrderedClosedTargetRamseyFamily_of_mem

end StructuralRamsey.Girth

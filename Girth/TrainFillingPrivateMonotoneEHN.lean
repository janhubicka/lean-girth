import Girth.ALinearRamsey

set_option Elab.async false

/-!
# Retaining the ordered EHN selected-target witness

The existing theorem
  closedTargetRamseyFamily_of_monotone_embeddings
applies an ORDERED Ramsey theorem, then forgets the auxiliary
linear-order relation when returning its closure embedding b.

Its exported ClosedTargetRamseyFamily does NOT assert that the
selected b is strictly monotone in the auxiliary orders. This
is sufficient for its stated abstract Ramsey theorem, but not
for the direct cutoff-two private filling, where the coordinate
maps F_p -> W -> X must respect the chosen global orders.

The proof below records the stronger statement that is already
available from the original ordered EHN construction: for every
A-colouring there is an ORDER-preserving closure embedding of W.
We keep the witness itself and its strict monotonicity instead
of discarding the order and then assuming it can be recovered.

The ordinary ClosedTargetRamseyFamily follows by forgetting this
property. The next module can restrict the indexed EHN choices to
this monotone family, without imposing monotonicity on ALL
closure embeddings (which would be false in general).

These declarations are source candidates until an exact-head
local Lean build and #print axioms audit.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}

/-- The closed-target EHN Ramsey arrow with the very SAME chosen
target embedding required to be increasing in the auxiliary
linear orders. The target order is an explicit parameter so that
the existentially produced X-order cannot be silently forgotten. -/
def MonotoneClosedTargetRamseyFamily
    (A : RelStructure L U) (B : RelStructure L V)
    {X : Type v} [LinearOrder V]
    (o : LinearOrder X)
    (C : StructuralRamsey.Structure (closureLanguage L) X)
    (κ : Type*) : Prop :=
  letI : LinearOrder X := o
  ∀ χ : RelStructure.Embedding A (closureRelReduct C) → κ,
    ∃ b : StructuralRamsey.Structure.Embedding
        (targetClosureExpansion A B) C,
      StrictMono (targetEmbeddingRel b) ∧
      ∀ a₁ a₂ : RelStructure.Embedding A B,
        χ ((targetEmbeddingRel b).comp a₁) =
          χ ((targetEmbeddingRel b).comp a₂)

/-- Stronger form of the existing EHN theorem: the same Ramsey
selection is monotone because it is the reduct of the actual
ORDERED embedding returned by orderedRamsey_of_mem_target.
The proof duplicates only the EHN witness passage that the
ordinary export forgets; no new Ramsey input or axiom. -/
theorem monotoneClosedTargetRamseyFamily_of_monotone_embeddings
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V]
    [Finite U] [Finite V]
    (hAirr : A.Irreducible)
    (hBlin : ALinear A B)
    (hmono : ∀ a : RelStructure.Embedding A B, StrictMono a)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X)
      (C : StructuralRamsey.Structure (closureLanguage L) X),
      ElementaryCAClass A C ∧
      MonotoneClosedTargetRamseyFamily A B o C κ := by
  classical
  let K : StructuralRamsey.Structure.StructureClass.{u,v}
      (L := closureLanguage L) := ElementaryCAClass A
  have hK : StructuralRamsey.Structure.FreeAmalgamationClass K :=
    ElementaryCAClass_freeAmalgamationClass A hAirr
  let Ahat := targetClosureExpansion A A
  let Bhat := targetClosureExpansion A B
  have hBmem : K Bhat := targetClosure_mem_ElementaryCAClass hBlin
  obtain ⟨X, hX, o, C, hCmem, hRamsey⟩ :=
    hK.orderedRamsey_of_mem_target
      Ahat Bhat hBmem closureLanguage_positiveFuncArity κ
  letI : Finite X := hX
  letI : LinearOrder X := o
  refine ⟨X, hX, o, C, hCmem, ?_⟩
  change ∀ χ : RelStructure.Embedding A (closureRelReduct C) → κ,
    ∃ b : StructuralRamsey.Structure.Embedding
        (targetClosureExpansion A B) C,
      StrictMono (targetEmbeddingRel b) ∧
      ∀ a₁ a₂ : RelStructure.Embedding A B,
        χ ((targetEmbeddingRel b).comp a₁) =
          χ ((targetEmbeddingRel b).comp a₂)
  intro χ
  let χhat :
      StructuralRamsey.Structure.Embedding
        Ahat.withLinearOrder C.withLinearOrder → κ :=
    fun e => χ (targetEmbeddingRel e.linearOrderReduct)
  obtain ⟨b, hb⟩ := hRamsey χhat
  let b0 : StructuralRamsey.Structure.Embedding Bhat C :=
    b.linearOrderReduct
  have hbMono : StrictMono (targetEmbeddingRel b0) := by
    intro x y hxy
    have hOrder :=
      (b.map_rel_iff (.inr ()) ![x, y]).mpr (by
        change x < y
        exact hxy)
    change (targetEmbeddingRel b0) x < (targetEmbeddingRel b0) y
      at hOrder
    exact hOrder
  refine ⟨b0, hbMono, ?_⟩
  intro a₁ a₂
  let a₁f :
      StructuralRamsey.Structure.Embedding Ahat Bhat :=
    targetClosureLift hBlin a₁
  let a₂f :
      StructuralRamsey.Structure.Embedding Ahat Bhat :=
    targetClosureLift hBlin a₂
  let a₁o :
      StructuralRamsey.Structure.Embedding
        Ahat.withLinearOrder Bhat.withLinearOrder :=
    structureEmbeddingWithLinearOrder a₁f (hmono a₁)
  let a₂o :
      StructuralRamsey.Structure.Embedding
        Ahat.withLinearOrder Bhat.withLinearOrder :=
    structureEmbeddingWithLinearOrder a₂f (hmono a₂)
  have hc := hb a₁o a₂o
  have hcomp₁ :
      targetEmbeddingRel ((b.comp a₁o).linearOrderReduct) =
        (targetEmbeddingRel b0).comp a₁ := by
    apply RelStructure.Embedding.ext
    intro x
    rfl
  have hcomp₂ :
      targetEmbeddingRel ((b.comp a₂o).linearOrderReduct) =
        (targetEmbeddingRel b0).comp a₂ := by
    apply RelStructure.Embedding.ext
    intro x
    rfl
  change
    χ (targetEmbeddingRel ((b.comp a₁o).linearOrderReduct)) =
      χ (targetEmbeddingRel ((b.comp a₂o).linearOrderReduct))
    at hc
  calc
    χ ((targetEmbeddingRel b0).comp a₁) =
        χ (targetEmbeddingRel ((b.comp a₁o).linearOrderReduct)) :=
      congrArg χ hcomp₁.symm
    _ = χ (targetEmbeddingRel ((b.comp a₂o).linearOrderReduct)) := hc
    _ = χ ((targetEmbeddingRel b0).comp a₂) :=
      congrArg χ hcomp₂

/-- Forgetting the extra order certificate recovers exactly the
previously checked closed-target Ramsey family proposition. -/
theorem MonotoneClosedTargetRamseyFamily.toClosedTargetRamseyFamily
    (A : RelStructure L U) (B : RelStructure L V)
    {X : Type v} [LinearOrder V]
    (o : LinearOrder X)
    (C : StructuralRamsey.Structure (closureLanguage L) X)
    (κ : Type*)
    (h : MonotoneClosedTargetRamseyFamily A B o C κ) :
    ClosedTargetRamseyFamily A B C κ := by
  intro χ
  obtain ⟨b, _, hmono⟩ := h χ
  exact ⟨b, hmono⟩

end StructuralRamsey.Girth

import Girth.FunctionalEHNClass
import Girth.ClosureLift
import Girth.ClosureEmbeddingGeometry
import PartiteConstruction.Ramsey.FreeAmalgamationFunctions
import PartiteConstruction.Relational.Order
import PartiteConstruction.Iterated.Ordered

/-! # The A-linear Ramsey theorem from functional EHN

The functional EHN theorem is applied to the class of full structures whose
relational reduct is A-linear and whose binary closure c_A is canonical.  The
ternary symbol c_B is unconstrained in the class and is prescribed only on the
target.  This is exactly the manuscript's fixed-target construction.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}

/-- Add the fresh EHN order to a full embedding when its underlying map is
strictly monotone. -/
def structureEmbeddingWithLinearOrder
    {K : StructuralRamsey.Language.{u}}
    {X Y : Type v}
    {A : StructuralRamsey.Structure K X}
    {B : StructuralRamsey.Structure K Y}
    [LinearOrder X] [LinearOrder Y]
    (e : StructuralRamsey.Structure.Embedding A B)
    (hmono : StrictMono e) :
    StructuralRamsey.Structure.Embedding
      A.withLinearOrder B.withLinearOrder where
  toFun := e
  injective := e.injective
  map_rel_iff R x := by
    cases R with
    | inl R =>
        exact e.map_rel_iff R x
    | inr _ =>
        exact hmono.lt_iff_lt
  map_func := e.map_func

@[simp]
theorem structureEmbeddingWithLinearOrder_apply
    {K : StructuralRamsey.Language.{u}}
    {X Y : Type v}
    {A : StructuralRamsey.Structure K X}
    {B : StructuralRamsey.Structure K Y}
    [LinearOrder X] [LinearOrder Y]
    (e : StructuralRamsey.Structure.Embedding A B)
    (hmono : StrictMono e) (x : X) :
    structureEmbeddingWithLinearOrder e hmono x = e x :=
  rfl


/-- The Ramsey family singled out by the target closure expansion.  A colouring
of relational A-embeddings is witnessed by a full closed embedding of the
expanded target B; hence the same witnesses inherit the closure geometry. -/
def ClosedTargetRamseyFamily
    (A : RelStructure L U) (B : RelStructure L V)
    {W : Type v}
    (C : StructuralRamsey.Structure (closureLanguage L) W)
    (κ : Type*) : Prop :=
  ∀ χ : RelStructure.Embedding A (closureRelReduct C) → κ,
    ∃ b : StructuralRamsey.Structure.Embedding
        (targetClosureExpansion A B) C,
      ∀ a₁ a₂ : RelStructure.Embedding A B,
        χ ((targetEmbeddingRel b).comp a₁) =
          χ ((targetEmbeddingRel b).comp a₂)

/-- A closed-target Ramsey family is, after forgetting the closure structure,
an ordinary Ramsey arrow. -/
theorem ClosedTargetRamseyFamily.arrow
    {A : RelStructure L U} {B : RelStructure L V}
    {W : Type v}
    {C : StructuralRamsey.Structure (closureLanguage L) W}
    {κ : Type*}
    (h : ClosedTargetRamseyFamily A B C κ) :
    StructuralRamsey.Arrow A B (closureRelReduct C) κ := by
  intro χ
  obtain ⟨b, hb⟩ := h χ
  exact ⟨targetEmbeddingRel b, hb⟩

/-- Functional EHN produces the stronger closed-target Ramsey family used in
the manuscript.  The monotonicity hypothesis is exactly what lets every
relational A-embedding into B lift through the fresh auxiliary order. -/
theorem closedTargetRamseyFamily_of_monotone_embeddings
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V]
    [Finite U] [Finite V]
    (hAirr : A.Irreducible)
    (hBlin : ALinear A B)
    (hmono : ∀ a : RelStructure.Embedding A B, StrictMono a)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : StructuralRamsey.Structure (closureLanguage L) W),
      ElementaryCAClass A C ∧
      ClosedTargetRamseyFamily A B C κ := by
  classical
  let K : StructuralRamsey.Structure.StructureClass.{u,v}
      (L := closureLanguage L) := ElementaryCAClass A
  have hK :
      StructuralRamsey.Structure.FreeAmalgamationClass K :=
    ElementaryCAClass_freeAmalgamationClass A hAirr
  let Ahat := targetClosureExpansion A A
  let Bhat := targetClosureExpansion A B
  have hBmem : K Bhat :=
    targetClosure_mem_ElementaryCAClass hBlin
  obtain ⟨W, hW, o, C, hCmem, hRamsey⟩ :=
    hK.orderedRamsey_of_mem_target
      Ahat Bhat hBmem closureLanguage_positiveFuncArity κ
  letI : Finite W := hW
  letI : LinearOrder W := o
  refine ⟨W, hW, o, C, hCmem, ?_⟩
  intro χ
  let χhat :
      StructuralRamsey.Structure.Embedding
        Ahat.withLinearOrder C.withLinearOrder → κ :=
    fun e => χ (targetEmbeddingRel e.linearOrderReduct)
  obtain ⟨b, hb⟩ := hRamsey χhat
  let b0 :
      StructuralRamsey.Structure.Embedding Bhat C :=
    b.linearOrderReduct
  refine ⟨b0, ?_⟩
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
      targetEmbeddingRel
          ((b.comp a₁o).linearOrderReduct) =
        (targetEmbeddingRel b0).comp a₁ := by
    apply RelStructure.Embedding.ext
    intro x
    rfl
  have hcomp₂ :
      targetEmbeddingRel
          ((b.comp a₂o).linearOrderReduct) =
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


/-- Functional EHN gives the manuscript's A-linear Ramsey input whenever the
chosen external linear orders are respected by every A-embedding into B.

The witness is returned together with its full closure structure.  In
particular every full target embedding has A-strong reduct, and two distinct
such embeddings have controlled A-linear intersections. -/
theorem aLinearRamsey_of_monotone_embeddings
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V]
    [Finite U] [Finite V]
    (hAirr : A.Irreducible)
    (hBlin : ALinear A B)
    (hmono :
      ∀ a : RelStructure.Embedding A B, StrictMono a)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : StructuralRamsey.Structure (closureLanguage L) W),
      ElementaryCAClass A C ∧
      StructuralRamsey.Arrow A B (closureRelReduct C) κ ∧
      (∀ b : StructuralRamsey.Structure.Embedding
          (targetClosureExpansion A B) C,
        AStrong A (closureRelReduct C)
          (copyCarrier (targetEmbeddingRel b))) ∧
      (∀ b c : StructuralRamsey.Structure.Embedding
          (targetClosureExpansion A B) C,
        ¬ SameCopy (targetEmbeddingRel b) (targetEmbeddingRel c) →
          (copyCarrier (targetEmbeddingRel b) ∩
              copyCarrier (targetEmbeddingRel c)).Subsingleton ∨
            ∃ a : RelStructure.Embedding A (closureRelReduct C),
              copyCarrier (targetEmbeddingRel b) ∩
                copyCarrier (targetEmbeddingRel c) =
                  copyCarrier a) := by
  classical
  let K : StructuralRamsey.Structure.StructureClass.{u,v}
      (L := closureLanguage L) := ElementaryCAClass A
  have hK :
      StructuralRamsey.Structure.FreeAmalgamationClass K :=
    ElementaryCAClass_freeAmalgamationClass A hAirr
  let Ahat := targetClosureExpansion A A
  let Bhat := targetClosureExpansion A B
  have hBmem : K Bhat :=
    targetClosure_mem_ElementaryCAClass hBlin
  obtain ⟨W, hW, o, C, hCmem, hRamsey⟩ :=
    hK.orderedRamsey_of_mem_target
      Ahat Bhat hBmem closureLanguage_positiveFuncArity κ
  letI : Finite W := hW
  letI : LinearOrder W := o
  have hRelArrow :
      StructuralRamsey.Arrow A B (closureRelReduct C) κ := by
    intro χ
    let χhat :
        StructuralRamsey.Structure.Embedding
          Ahat.withLinearOrder C.withLinearOrder → κ :=
      fun e => χ (targetEmbeddingRel e.linearOrderReduct)
    obtain ⟨b, hb⟩ := hRamsey χhat
    let b0 :
        StructuralRamsey.Structure.Embedding Bhat C :=
      b.linearOrderReduct
    let br : RelStructure.Embedding B (closureRelReduct C) :=
      targetEmbeddingRel b0
    refine ⟨br, ?_⟩
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
    have hmonoColour := hb a₁o a₂o
    have hcomp₁ :
        targetEmbeddingRel
            ((b.comp a₁o).linearOrderReduct) =
          br.comp a₁ := by
      apply RelStructure.Embedding.ext
      intro x
      rfl
    have hcomp₂ :
        targetEmbeddingRel
            ((b.comp a₂o).linearOrderReduct) =
          br.comp a₂ := by
      apply RelStructure.Embedding.ext
      intro x
      rfl
    change
      χ (targetEmbeddingRel ((b.comp a₁o).linearOrderReduct)) =
        χ (targetEmbeddingRel ((b.comp a₂o).linearOrderReduct))
      at hmonoColour
    calc
      χ (br.comp a₁) =
          χ (targetEmbeddingRel ((b.comp a₁o).linearOrderReduct)) :=
        congrArg χ hcomp₁.symm
      _ =
          χ (targetEmbeddingRel ((b.comp a₂o).linearOrderReduct)) :=
        hmonoColour
      _ = χ (br.comp a₂) :=
        congrArg χ hcomp₂
  refine ⟨W, hW, o, C, hCmem, hRelArrow, ?_, ?_⟩
  · intro b
    exact targetEmbedding_range_aStrong hCmem.2 b
  · intro b c hne
    exact targetEmbeddings_controlledIntersection
      hBlin b c hne

/-- Standard ordered-structure specialization.  Here the fresh external order
is the canonical order already added to the relational structures, so
irreducibility and monotonicity are automatic. -/
theorem aLinearRamsey_ordered
    (A₀ : RelStructure L U) (B₀ : RelStructure L V)
    [LinearOrder U] [LinearOrder V]
    [Finite U] [Finite V]
    (hBlin : ALinear A₀.ordered B₀.ordered)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : StructuralRamsey.Structure
        (closureLanguage L.withOrder) W),
      ElementaryCAClass A₀.ordered C ∧
      StructuralRamsey.Arrow
        A₀.ordered B₀.ordered (closureRelReduct C) κ ∧
      (∀ b : StructuralRamsey.Structure.Embedding
          (targetClosureExpansion A₀.ordered B₀.ordered) C,
        AStrong A₀.ordered (closureRelReduct C)
          (copyCarrier (targetEmbeddingRel b))) ∧
      (∀ b c : StructuralRamsey.Structure.Embedding
          (targetClosureExpansion A₀.ordered B₀.ordered) C,
        ¬ SameCopy (targetEmbeddingRel b) (targetEmbeddingRel c) →
          (copyCarrier (targetEmbeddingRel b) ∩
              copyCarrier (targetEmbeddingRel c)).Subsingleton ∨
            ∃ a : RelStructure.Embedding A₀.ordered (closureRelReduct C),
              copyCarrier (targetEmbeddingRel b) ∩
                copyCarrier (targetEmbeddingRel c) =
                  copyCarrier a) := by
  apply aLinearRamsey_of_monotone_embeddings
    A₀.ordered B₀.ordered
  · exact (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  · exact hBlin
  · intro a
    exact RelStructure.Embedding.strictMono a

end StructuralRamsey.Girth

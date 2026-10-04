import Girth.ElementaryClosureAmalgam
import Girth.ClosureEmbeddingGeometry
import PartiteConstruction.Ramsey.FreeAmalgamationFunctions

/-! # The functional EHN class for A-linear structures

The Ramsey-input class remembers only two pieces of data:
* the relational reduct is A-linear;
* c_A has its canonical elementary-closure interpretation.

The ternary c_B symbol is deliberately unconstrained.  This is exactly the
class used in the manuscript's fixed-target EHN argument.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U X Y : Type v}

/-- Forget the two closure functions from an arbitrary full structure in the
closure language. -/
def closureEmbeddingRel
    {C : StructuralRamsey.Structure (closureLanguage L) X}
    {D : StructuralRamsey.Structure (closureLanguage L) Y}
    (e : StructuralRamsey.Structure.Embedding C D) :
    RelStructure.Embedding (closureRelReduct C) (closureRelReduct D) where
  toFun := e
  injective := e.injective
  map_rel_iff R x := e.map_rel_iff R x

/-- Forget the closure functions from a full free-amalgam diagram. -/
theorem closureFreeAmalgamRel
    {H E F C : Type v}
    {Base : StructuralRamsey.Structure (closureLanguage L) H}
    {Left : StructuralRamsey.Structure (closureLanguage L) E}
    {Right : StructuralRamsey.Structure (closureLanguage L) F}
    {Whole : StructuralRamsey.Structure (closureLanguage L) C}
    {sL : StructuralRamsey.Structure.Embedding Base Left}
    {sR : StructuralRamsey.Structure.Embedding Base Right}
    {iL : StructuralRamsey.Structure.Embedding Left Whole}
    {iR : StructuralRamsey.Structure.Embedding Right Whole}
    (hfree : StructuralRamsey.Structure.IsFreeAmalgam sL sR iL iR) :
    RelStructure.IsFreeAmalgam
      (closureEmbeddingRel sL) (closureEmbeddingRel sR)
      (closureEmbeddingRel iL) (closureEmbeddingRel iR) where
  covers := hfree.covers
  overlap := hfree.overlap
  rel_iff R x := hfree.rel_iff R x

/-- A-linearity pulls back along an arbitrary induced embedding. -/
theorem aLinear_of_embedding
    {A : RelStructure L U}
    {D : RelStructure L X} {E : RelStructure L Y}
    (hD : ALinear A E) (e : RelStructure.Embedding D E) :
    ALinear A D := by
  intro a b hne
  have hne' : ¬ SameCopy (e.comp a) (e.comp b) := by
    intro h
    exact hne (sameCopy_of_comp e h)
  have hs := hD (e.comp a) (e.comp b) hne'
  intro x hx y hy
  apply e.injective
  apply hs
  · rcases hx.1 with ⟨a0, ha0⟩
    rcases hx.2 with ⟨b0, hb0⟩
    constructor
    · exact ⟨a0, congrArg e ha0⟩
    · exact ⟨b0, congrArg e hb0⟩
  · rcases hy.1 with ⟨a0, ha0⟩
    rcases hy.2 with ⟨b0, hb0⟩
    constructor
    · exact ⟨a0, congrArg e ha0⟩
    · exact ⟨b0, congrArg e hb0⟩

/-- Full embeddings into a structure with canonical c_A have A-strong
relational ranges. -/
theorem closureEmbedding_range_aStrong
    {A : RelStructure L U}
    {C : StructuralRamsey.Structure (closureLanguage L) X}
    {D : StructuralRamsey.Structure (closureLanguage L) Y}
    (hCA : HasElementaryCA A D)
    (e : StructuralRamsey.Structure.Embedding C D) :
    AStrong A (closureRelReduct D)
      (copyCarrier (closureEmbeddingRel e)) := by
  have hRange := StructuralRamsey.Structure.Embedding.range_isClosed e
  apply (pairClosed_iff_aStrong A (closureRelReduct D)
    (copyCarrier (closureEmbeddingRel e))).mp
  intro x hx y hy hxy a hxa hya z hz
  let t2 : Fin 2 → Y := ![x, y]
  let t := cAInput (L := L) t2
  have ht2 : ∀ i : Fin 2, t2 i ∈ Set.range e := by
    intro i
    fin_cases i
    · exact hx
    · exact hy
  have ht : ∀ i, t i ∈ Set.range e := by
    simpa [t, cAInput, closureLanguage] using ht2
  have hzValue : z ∈ cAValue A (closureRelReduct D) t2 :=
    ⟨hxy, a, hxa, hya, hz⟩
  have hzFunc :
      z ∈ D.func (ClosureFunc.cA : ClosureFunc.{u}) t := by
    rw [hCA t2]
    exact hzValue
  exact hRange (ClosureFunc.cA : ClosureFunc.{u}) t ht hzFunc

/-- Canonical c_A semantics pull back along every full embedding into an
A-linear member of the class. -/
theorem hasElementaryCA_of_embedding
    {A : RelStructure L U}
    {C : StructuralRamsey.Structure (closureLanguage L) X}
    {D : StructuralRamsey.Structure (closureLanguage L) Y}
    (hLinear : ALinear A (closureRelReduct D))
    (hCA : HasElementaryCA A D)
    (e : StructuralRamsey.Structure.Embedding C D) :
    HasElementaryCA A C := by
  let er : RelStructure.Embedding (closureRelReduct C) (closureRelReduct D) :=
    closureEmbeddingRel e
  have hStrong :
      AStrong A (closureRelReduct D) (copyCarrier er) :=
    closureEmbedding_range_aStrong hCA e
  let ec :=
    elementaryClosureEmbeddingOfStrong er hStrong
  intro x
  have htuple :
      e ∘ cAInput (L := L) x =
        cAInput (L := L) (e ∘ x) := by
    funext i
    fin_cases i <;> rfl
  have hActual :
      StructuralRamsey.Structure.imageSet e
          (C.func (ClosureFunc.cA : ClosureFunc.{u})
            (cAInput (L := L) x)) =
        cAValue A (closureRelReduct D) (e ∘ x) := by
    rw [e.map_func (ClosureFunc.cA : ClosureFunc.{u})
      (cAInput (L := L) x)]
    rw [htuple]
    exact hCA (e ∘ x)
  have hCanon :
      StructuralRamsey.Structure.imageSet e
          (cAValue A (closureRelReduct C) x) =
        cAValue A (closureRelReduct D) (e ∘ x) := by
    have h := ec.map_func (ClosureFunc.cA : ClosureFunc.{u})
      (cAInput (L := L) x)
    simpa [ec, elementaryClosureExpansion, cAInput, closureLanguage,
      htuple] using h
  apply Set.ext
  intro y
  constructor
  · intro hy
    have hey :
        e y ∈ StructuralRamsey.Structure.imageSet e
          (C.func (ClosureFunc.cA : ClosureFunc.{u})
            (cAInput (L := L) x)) :=
      ⟨y, hy, rfl⟩
    rw [hActual, ← hCanon] at hey
    rcases hey with ⟨z, hz, heq⟩
    have hzy : z = y := e.injective heq
    simpa [hzy] using hz
  · intro hy
    have hey :
        e y ∈ StructuralRamsey.Structure.imageSet e
          (cAValue A (closureRelReduct C) x) :=
      ⟨y, hy, rfl⟩
    rw [hCanon, ← hActual] at hey
    rcases hey with ⟨z, hz, heq⟩
    have hzy : z = y := e.injective heq
    simpa [hzy] using hz

/-- The class used for the functional EHN theorem: A-linear reduct and
canonical c_A, with no condition at all on c_B. -/
def ElementaryCAClass
    (A : RelStructure L U) :
    StructuralRamsey.Structure.StructureClass
      (L := closureLanguage L) :=
  fun C =>
    ALinear A (closureRelReduct C) ∧ HasElementaryCA A C

/-- The actual target closure expansion belongs to the elementary class. -/
theorem targetClosure_mem_ElementaryCAClass
    {A : RelStructure L U} {B : RelStructure L X}
    (hB : ALinear A B) :
    ElementaryCAClass A (targetClosureExpansion A B) := by
  constructor
  · simpa [closureRelReduct, targetClosureExpansion] using hB
  · intro x
    rfl

/-- Our closure language has positive function arities (2 and 3). -/
theorem closureLanguage_positiveFuncArity :
    (closureLanguage L).PositiveFuncArity := by
  intro F
  cases F <;> simp [closureLanguage]

/-- The elementary c_A class is hereditary and closed under full free
amalgamation.  The ternary c_B fibres are inherited freely but otherwise
unrestricted. -/
theorem ElementaryCAClass_freeAmalgamationClass
    (A : RelStructure L U) (hA : A.Irreducible) :
    StructuralRamsey.Structure.FreeAmalgamationClass
      (ElementaryCAClass A) := by
  constructor
  · intro X Y C D hD e
    exact ⟨
      aLinear_of_embedding hD.1 (closureEmbeddingRel e),
      hasElementaryCA_of_embedding hD.1 hD.2 e⟩
  · intro H E F C Base Left Right Whole sL sR iL iR
      hLeft hRight hfree
    let sLr := closureEmbeddingRel sL
    let sRr := closureEmbeddingRel sR
    let iLr := closureEmbeddingRel iL
    let iRr := closureEmbeddingRel iR
    have hfreeRel :
        RelStructure.IsFreeAmalgam sLr sRr iLr iRr :=
      closureFreeAmalgamRel hfree
    have hBaseL :
        AStrong A (closureRelReduct Left) (copyCarrier sLr) :=
      closureEmbedding_range_aStrong hLeft.2 sL
    have hBaseR :
        AStrong A (closureRelReduct Right) (copyCarrier sRr) :=
      closureEmbedding_range_aStrong hRight.2 sR
    have hStrongL :
        AStrong A (closureRelReduct Whole) (copyCarrier iLr) :=
      freeAmalgam_left_aStrong hA hBaseR hfreeRel
    have hStrongR :
        AStrong A (closureRelReduct Whole) (copyCarrier iRr) :=
      freeAmalgam_right_aStrong hA hBaseL hfreeRel
    have hLinear :
        ALinear A (closureRelReduct Whole) :=
      aLinear_of_freeAmalgam hA hLeft.1 hRight.1
        hBaseL hBaseR hfreeRel
    refine ⟨hLinear, ?_⟩
    intro x
    let canonFree :=
      elementaryClosure_isFreeAmalgam hA hBaseL hBaseR hfreeRel
    apply Set.ext
    intro y
    have hActual :=
      hfree.func_iff (ClosureFunc.cA : ClosureFunc.{u})
        (cAInput (L := L) x) y
    have hCanon :=
      canonFree.func_iff (ClosureFunc.cA : ClosureFunc.{u})
        (cAInput (L := L) x) y
    simp only [closureLanguage] at hActual hCanon
    constructor
    · intro hy
      rcases hActual.mp hy with
        ⟨args, b, hb, hargs, hout⟩ |
        ⟨args, b, hb, hargs, hout⟩
      · have hb' : b ∈ cAValue A (closureRelReduct Left) args := by
          have hEq := hLeft.2 args
          change b ∈ Left.func (ClosureFunc.cA : ClosureFunc.{u})
            (cAInput (L := L) args) at hb
          rw [hEq] at hb
          exact hb
        have hcanonSide :
            b ∈ (elementaryClosureExpansion A
              (closureRelReduct Left)).func
              (ClosureFunc.cA : ClosureFunc.{u}) args := by
          exact hb'
        have hyCanon :
            y ∈ (elementaryClosureExpansion A
              (closureRelReduct Whole)).func
              (ClosureFunc.cA : ClosureFunc.{u})
              (cAInput (L := L) x) := by
          apply hCanon.mpr
          left
          refine ⟨args, b, hcanonSide, ?_, ?_⟩
          · exact hargs
          · exact hout
        exact hyCanon
      · have hb' : b ∈ cAValue A (closureRelReduct Right) args := by
          have hEq := hRight.2 args
          change b ∈ Right.func (ClosureFunc.cA : ClosureFunc.{u})
            (cAInput (L := L) args) at hb
          rw [hEq] at hb
          exact hb
        have hcanonSide :
            b ∈ (elementaryClosureExpansion A
              (closureRelReduct Right)).func
              (ClosureFunc.cA : ClosureFunc.{u}) args := by
          exact hb'
        have hyCanon :
            y ∈ (elementaryClosureExpansion A
              (closureRelReduct Whole)).func
              (ClosureFunc.cA : ClosureFunc.{u})
              (cAInput (L := L) x) := by
          apply hCanon.mpr
          right
          refine ⟨args, b, hcanonSide, ?_, ?_⟩
          · exact hargs
          · exact hout
        exact hyCanon
    · intro hy
      change y ∈ cAValue A (closureRelReduct Whole) x at hy
      have hyCanon :
          y ∈ (elementaryClosureExpansion A
            (closureRelReduct Whole)).func
            (ClosureFunc.cA : ClosureFunc.{u})
            (cAInput (L := L) x) := hy
      rcases hCanon.mp hyCanon with
        ⟨args, b, hb, hargs, hout⟩ |
        ⟨args, b, hb, hargs, hout⟩
      · have hb' : b ∈ Left.func
            (ClosureFunc.cA : ClosureFunc.{u})
            (cAInput (L := L) args) := by
          have hEq := hLeft.2 args
          rw [hEq]
          exact hb
        apply hActual.mpr
        left
        exact ⟨args, b, hb', hargs, hout⟩
      · have hb' : b ∈ Right.func
            (ClosureFunc.cA : ClosureFunc.{u})
            (cAInput (L := L) args) := by
          have hEq := hRight.2 args
          rw [hEq]
          exact hb
        apply hActual.mpr
        right
        exact ⟨args, b, hb', hargs, hout⟩

end StructuralRamsey.Girth

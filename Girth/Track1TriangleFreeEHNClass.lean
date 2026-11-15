import Girth.Track1StrongAmalgamGirthThree
import Girth.FunctionalEHNClass
import Girth.SupportGirthEmbeddingEquiv

/-!
# Track 1: canonical pair-closure class restricted to girth > 3

The ternary c_B remains UNCONSTRAINED in this EHN class. This is the
class used for the unmarked auxiliary Ramsey theorem with high girth.
The additional girth condition belongs to the relational A-support.

This file uses the draft concrete A-strong relational amalgam girth
theorem; it is not yet a kernel certificate. No extra unary function
or new closure language is introduced.

DRAFT, NOT COMPILED. The new files need focused Lean and axiom checks.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U : Type v}

/-- The existing elementary canonical c_A class, further restricted to
support girth strictly greater than three. Arbitrary c_B values remain
permitted, and the external EHN theorem is an explicit dependency. -/
def ElementaryCAThreeClass (A : RelStructure L U) :
    StructuralRamsey.Structure.StructureClass
      (L := closureLanguage L) :=
  fun C => ElementaryCAClass A C ∧
    GirthGT (supportCopies A (closureRelReduct C)) 3

/-- The target expansion belongs to the restricted class whenever
its ordinary A-support has girth >3. -/
theorem targetClosure_mem_ElementaryCAThreeClass
    {A : RelStructure L U} {V : Type v}
    {B : RelStructure L V}
    (hLinear : ALinear A B)
    (hGirth : GirthGT (supportCopies A B) 3) :
    ElementaryCAThreeClass A (targetClosureExpansion A B) := by
  refine ⟨targetClosure_mem_ElementaryCAClass hLinear, ?_⟩
  simpa [ElementaryCAThreeClass, closureRelReduct,
    targetClosureExpansion] using hGirth

/-- The triangle-free restriction is hereditary and closed under
A-strong free amalgamation, with arbitrary c_B fibres. -/
theorem ElementaryCAThreeClass_freeAmalgamationClass
    (A : RelStructure L U) (hA : A.Irreducible) :
    StructuralRamsey.Structure.FreeAmalgamationClass
      (ElementaryCAThreeClass A) := by
  let hK :
      StructuralRamsey.Structure.FreeAmalgamationClass
        (ElementaryCAClass A) :=
    ElementaryCAClass_freeAmalgamationClass A hA
  constructor
  · intro X Y C D hD e
    refine ⟨hK.hereditary hD.1 e, ?_⟩
    let er := closureEmbeddingRel e
    have hSub :
        mappedSupportCopies A (closureRelReduct C)
          (closureRelReduct D) er ⊆
          supportCopies A (closureRelReduct D) := by
      rintro s ⟨a, rfl⟩
      exact ⟨er.comp a, rfl⟩
    have hMapped :
        GirthGT
          (mappedSupportCopies A (closureRelReduct C)
            (closureRelReduct D) er) 3 :=
      girthGT_of_subset hSub hD.2
    exact girthGT_source_of_mappedSupportCopies
      A (closureRelReduct C) (closureRelReduct D) er 3 hMapped
  · intro H E F C Base Left Right Whole sL sR iL iR
      hLeft hRight hfree
    have hRelFree :
        RelStructure.IsFreeAmalgam
          (closureEmbeddingRel sL) (closureEmbeddingRel sR)
          (closureEmbeddingRel iL) (closureEmbeddingRel iR) :=
      closureFreeAmalgamRel hfree
    have hBaseL :
        AStrong A (closureRelReduct Left)
          (copyCarrier (closureEmbeddingRel sL)) :=
      closureEmbedding_range_aStrong hLeft.1.2 sL
    have hBaseR :
        AStrong A (closureRelReduct Right)
          (copyCarrier (closureEmbeddingRel sR)) :=
      closureEmbedding_range_aStrong hRight.1.2 sR
    have hGirth :
        GirthGT (supportCopies A (closureRelReduct Whole)) 3 :=
      track1_girthGT_three_freeAmalgam_of_aStrong
        hA hLeft.1.1 hRight.1.1
        hBaseL hBaseR hLeft.2 hRight.2 hRelFree
    exact ⟨hK.free hLeft.1 hRight.1 hfree, hGirth⟩

#print axioms StructuralRamsey.Girth.targetClosure_mem_ElementaryCAThreeClass
#print axioms StructuralRamsey.Girth.ElementaryCAThreeClass_freeAmalgamationClass

end StructuralRamsey.Girth

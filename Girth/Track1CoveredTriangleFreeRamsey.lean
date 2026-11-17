import Girth.Track1TriangleFreeEHNClass
import Girth.Track1PhysicalSelectedRepresentatives
import Girth.TrainRecursiveCoveredClosureRamsey

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {U V : Type v}

/-- A triangle-free EHN witness can also cover its nonsingleton irreducibles.
Index the selected family once for each original physical target carrier. -/
theorem coveredTriangleFreeRamsey_physicalSelectedFamily
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hA : A.Irreducible) (hLinear : ALinear A B)
    (hGirth : GirthGT (supportCopies A B) 3)
    (hCoverage : NonsingletonIrreduciblesExtendTo A B)
    (hMono : ∀ a : Embedding A B, StrictMono a)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W)
      (D : RelStructure L W) (I : Type v) (_ : Finite I) (f : I → Embedding B D),
      GirthGT (supportCopies A D) 3 ∧
      NonsingletonIrreduciblesExtendTo A D ∧
      Function.Injective (fun i => copyCarrier (f i)) ∧
      (∀ i, AStrong A D (copyCarrier (f i))) ∧
      (∀ i j, i ≠ j →
        (copyCarrier (f i) ∩ copyCarrier (f j)).Subsingleton ∨
        ∃ a : Embedding A D, copyCarrier (f i) ∩ copyCarrier (f j) = copyCarrier a) ∧
      (∀ χ : Embedding A D → κ, ∃ i,
        ∀ a b : Embedding A B, χ ((f i).comp a) = χ ((f i).comp b)) := by
  classical
  let K : StructuralRamsey.Structure.StructureClass.{u,v} (L := closureLanguage L) :=
    fun C => ElementaryCAThreeClass A C ∧ CoveredElementaryCAClass A C
  have hK : StructuralRamsey.Structure.FreeAmalgamationClass K := by
    let h₁ := ElementaryCAThreeClass_freeAmalgamationClass A hA
    let h₂ := CoveredElementaryCAClass_freeAmalgamationClass A hA
    constructor
    · intro _ _ _ _ h e
      exact ⟨h₁.hereditary h.1 e, h₂.hereditary h.2 e⟩
    · intro _ _ _ _ _ _ _ _ _ _ _ _ hLeft hRight hFree
      exact ⟨h₁.free hLeft.1 hRight.1 hFree, h₂.free hLeft.2 hRight.2 hFree⟩
  have hB : K (targetClosureExpansion A B) :=
    ⟨targetClosure_mem_ElementaryCAThreeClass hLinear hGirth,
      targetClosure_mem_ElementaryCAClass hLinear, hCoverage⟩
  obtain ⟨W, hW, _, C, hClass, hRamsey⟩ :=
    closedTargetRamseyFamily_of_mem A B hK hB hLinear hMono κ
  letI : Finite W := hW
  let D := closureRelReduct C
  let family : Set (Embedding B D) := Set.range (fun b : StructuralRamsey.Structure.Embedding
    (targetClosureExpansion A B) C => targetEmbeddingRel b)
  let I := Track1PhysicalBCarrier family
  have hFiniteI : Finite I := Finite.of_injective Subtype.val Subtype.val_injective
  let f := track1_physicalRepresentative family
  refine ⟨W, hW, D, I, hFiniteI, f, hClass.1.2, hClass.2.2, ?_, ?_, ?_, ?_⟩
  · intro i j hEq
    by_contra hNe
    exact track1_physicalRepresentative_distinct family hNe hEq
  · intro i
    obtain ⟨b, hb⟩ := (track1_physicalRepresentative_spec family i).1
    change targetEmbeddingRel b = f i at hb
    rw [← hb]
    exact targetEmbedding_range_aStrong hClass.1.1.2 b
  · intro i j hNe
    obtain ⟨b, hb⟩ := (track1_physicalRepresentative_spec family i).1
    obtain ⟨c, hc⟩ := (track1_physicalRepresentative_spec family j).1
    change targetEmbeddingRel b = f i at hb
    change targetEmbeddingRel c = f j at hc
    rw [← hb, ← hc]
    apply targetEmbeddings_controlledIntersection hLinear b c
    rw [hb, hc]
    exact track1_physicalRepresentative_distinct family hNe
  · apply track1_physicalRepresentative_arrow A family
    intro χ
    obtain ⟨b, hb⟩ := hRamsey χ
    exact ⟨targetEmbeddingRel b, ⟨b, rfl⟩, hb⟩

#print axioms StructuralRamsey.Girth.coveredTriangleFreeRamsey_physicalSelectedFamily

end StructuralRamsey.Girth

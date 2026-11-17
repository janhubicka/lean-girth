import Girth.ALinearRamsey
import Girth.TrainRecursiveCoveredClosureClass

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {U V : Type v}

/-- The fixed-target EHN construction with nonsingleton irreducible coverage
of the whole ambient reduct. The family still consists of the literal
closure-preserving target embeddings. -/
theorem coveredClosedTargetRamseyFamily_of_monotone_embeddings
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hA : A.Irreducible) (hBLinear : ALinear A B)
    (hCoverage : NonsingletonIrreduciblesExtendTo A B)
    (hMono : ∀ a : Embedding A B, StrictMono a)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : StructuralRamsey.Structure (closureLanguage L) W),
      CoveredElementaryCAClass A C ∧ ClosedTargetRamseyFamily A B C κ :=
  closedTargetRamseyFamily_of_mem A B
    (CoveredElementaryCAClass_freeAmalgamationClass A hA)
    ⟨targetClosure_mem_ElementaryCAClass hBLinear, hCoverage⟩
    hBLinear hMono κ

end StructuralRamsey.Girth

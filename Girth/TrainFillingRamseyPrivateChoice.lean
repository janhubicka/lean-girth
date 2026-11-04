import Girth.ALinearRamsey
import Girth.TrainFillingPrivateUniform

set_option Elab.async false

/-!
# From the coloured Ramsey input to the first-wagon private geometry

The EHN-based closed-target Ramsey family supplies a witness X with
selected closed target embeddings W* into X. Its closure condition makes
those embeddings A-strong. The already checked relational private-template
constructor then gives every W* its own valid private first-wagon extension.

Thus strongness and local private scattering geometry are outputs of the
Ramsey input rather than further hypotheses. The only extra target
requirement is that W has no A-isolated vertices, the exact pointwise
coverage assumed in the cutoff-two argument.

This is not yet the contraction/filling of a shorter-train witness or
the final colour-word arrow in the global H.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {UA VB V P Q : Type v}

/-- The existing EHN Ramsey theorem already chooses a common X and a
selected closed-target Ramsey family, and every selected W* in that family
constructs a valid private first-wagon component with its proper-cut
scattering geometry. No output geometry is assumed. -/
theorem exists_colouredRamsey_privateChoiceGeometry
    (A : RelStructure L UA) (B : RelStructure L VB)
    [LinearOrder UA] [LinearOrder VB]
    [Finite UA] [Finite VB]
    (hAirr : A.Irreducible)
    (hBlin : ALinear A B)
    (hmono : ∀ a : RelStructure.Embedding A B, StrictMono a)
    (hCovered : ∀ x : VB,
      ∃ a : RelStructure.Embedding A B, x ∈ copyCarrier a)
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ VB)
    (parent : P → Q)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X)
      (C : StructuralRamsey.Structure (closureLanguage L) X),
      ElementaryCAClass A C ∧
      ClosedTargetRamseyFamily A B C κ ∧
      (∀ b : StructuralRamsey.Structure.Embedding
          (targetClosureExpansion A B) C,
        ∃ U : PrivateWagonInput V P X,
          Nonempty ((U.data parent).ComponentTargetGeometry PUnit.unit)) := by
  classical
  obtain ⟨X, hFinite, ord, C, hClass, hRamsey⟩ :=
    closedTargetRamseyFamily_of_monotone_embeddings
      A B hAirr hBlin hmono κ
  refine ⟨X, hFinite, ord, C, hClass, hRamsey, ?_⟩
  intro b
  let T : UniformPrivateTemplate VB X :=
    UniformPrivateTemplate.ofStrongEmbedding A B (closureRelReduct C)
      (targetEmbeddingRel b)
      (targetEmbedding_range_aStrong hClass.2 b) hCovered
  refine ⟨T.toPrivateWagonInput oldCarrier identify, ?_⟩
  exact ⟨T.componentGeometry oldCarrier identify parent⟩

end StructuralRamsey.Girth

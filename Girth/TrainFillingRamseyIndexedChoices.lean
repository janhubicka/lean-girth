import Girth.TrainFillingRamseyPrivateChoice
import Girth.TrainFillingIndexedChoiceRelational

set_option Elab.async false

/-!
# EHN produces the complete heterogeneous indexed choice family

The already checked closed-target Ramsey input gives one finite X and
ALL selected closed-target W* embeddings. It also provides A-strongness
for each selected target. The checked relational private-template
constructor converts the ENTIRE family at once into a function
c ↦ PrivateWagonInput, rather than choosing one arbitrary local witness
per copy.

This gives an actual family for the heterogeneous G0 construction. Each
chosen local coordinate range equals the corresponding selected W*
carrier, and every U c has the same ambient X support-edge family.

The prescribed first intersection parameter A1 still needs its separate
owner-incidence split. Contraction, selected M-copy realization into H,
and the final Ramsey arrow remain open.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB V P : Type v}

/-- The EHN coloured Ramsey input produces the whole indexed family of
private choice components with the correct selected W* coordinates.
No independent output strongness, pointwise coverage or component
geometry field is supplied by the caller. -/
theorem exists_colouredRamsey_indexedPrivateChoices
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
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X)
      (C : StructuralRamsey.Structure (closureLanguage L) X),
      ElementaryCAClass A C ∧
      ClosedTargetRamseyFamily A B C κ ∧
      ∃ (U :
        (StructuralRamsey.Structure.Embedding
          (targetClosureExpansion A B) C) →
          PrivateWagonInput V P X),
        (∀ b p,
          Set.range ((U b).coordinate p) =
            copyCarrier (targetEmbeddingRel b)) ∧
        (∀ b,
          (U b).templateEdges =
            supportCopies A (closureRelReduct C)) := by
  classical
  obtain ⟨X, hFinite, ord, C, hClass, hRamsey⟩ :=
    closedTargetRamseyFamily_of_monotone_embeddings
      A B hAirr hBlin hmono κ
  let Choice :=
    StructuralRamsey.Structure.Embedding (targetClosureExpansion A B) C
  let chosen : Choice → RelStructure.Embedding B (closureRelReduct C) :=
    fun b => targetEmbeddingRel b
  have hStrong : ∀ b : Choice,
      AStrong A (closureRelReduct C) (copyCarrier (chosen b)) := by
    intro b
    exact targetEmbedding_range_aStrong hClass.2 b
  let U : Choice → PrivateWagonInput V P X :=
    relationalPrivateChoices A B (closureRelReduct C)
      chosen hStrong hCovered oldCarrier identify
  refine ⟨X, hFinite, ord, C, hClass, hRamsey, U, ?_, ?_⟩
  · intro b p
    let T : UniformPrivateTemplate VB X :=
      UniformPrivateTemplate.ofStrongEmbedding A B (closureRelReduct C)
        (chosen b) (hStrong b) hCovered
    change Set.range (T.coordinate oldCarrier identify p) =
      Set.range T.star
    exact T.coordinate_range_eq oldCarrier identify p
  · intro b
    rfl

end StructuralRamsey.Girth

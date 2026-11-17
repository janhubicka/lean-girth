import Girth.TrainRecursiveWitnessPass
import Girth.Support
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Ramsey arrow on actual physical A-edges versus A-embeddings

The manuscript's F_t arrow colours the physical edge set
OldACarrierEdge A C. The checked finite picture-step API colours
all relational embeddings Embedding A C. These are not interchangeable
for arbitrary nonrigid A: two different A-embeddings can have the
same image carrier, so a physical colouring cannot distinguish them.

If A-embeddings into C are determined by their whole image carrier,
each physical edge has one canonical A-embedding, and an arbitrary
embedding colouring factors through the physical carrier map.
The generic theorem keeps this rigidity property explicit.
The ordered specialization derives it from the already checked
ordered_embedding_eq_of_sameCopy, with no extra Ramsey claim.

The resulting local arrow is exactly the hypothesis consumed by
ForestTailStage.activeAttachment_pictureStep_of_familyArrow.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}}
variable {UA X Y I : Type v}
variable {A : RelStructure L UA}
variable {B : RelStructure L X} {C : RelStructure L Y}
variable {κ : Type w}

/-- A colouring of actual physical support edges can be used to
homogenize all A-embeddings once the ambient A-copy is uniquely
specified by its image. Uses actual physical carrier labels
retained by the train, not a quotient of unrelated edges. -/
theorem embeddingArrow_of_physicalEdgeArrow
    (f : I → RelStructure.Embedding B C)
    (hCarrierRigid : ∀ a b : RelStructure.Embedding A C,
      SameCopy a b → a = b)
    (hPhysical :
      ∀ χ : OldACarrierEdge A C → κ,
        ∃ i : I,
          ∀ a b : RelStructure.Embedding A B,
            χ (actualEdge ((f i).comp a)) =
              χ (actualEdge ((f i).comp b))) :
    ∀ ψ : RelStructure.Embedding A C → κ,
      ∃ i : I,
        ∀ a b : RelStructure.Embedding A B,
          ψ ((f i).comp a) = ψ ((f i).comp b) := by
  classical
  let representative : OldACarrierEdge A C → RelStructure.Embedding A C :=
    fun edge => Classical.choose edge.2
  have hChoice (edge : OldACarrierEdge A C) :
      edge.1 = copyCarrier (representative edge) :=
    Classical.choose_spec edge.2
  have hRepresentative (a : RelStructure.Embedding A C) :
      representative (actualEdge a) = a := by
    apply hCarrierRigid
    change copyCarrier (representative (actualEdge a)) = copyCarrier a
    exact (hChoice (actualEdge a)).symm
  intro ψ
  let colour : OldACarrierEdge A C → κ :=
    fun edge => ψ (representative edge)
  obtain ⟨i, hi⟩ := hPhysical colour
  refine ⟨i, ?_⟩
  intro a b
  have hEq := hi a b
  change ψ (representative (actualEdge ((f i).comp a))) =
    ψ (representative (actualEdge ((f i).comp b))) at hEq
  rw [hRepresentative ((f i).comp a),
    hRepresentative ((f i).comp b)] at hEq
  exact hEq

/-- Exactly the same bridge without the SameCopy abbreviation:
injectivity of the actual physical support-label map is sufficient. -/
theorem embeddingArrow_of_physicalEdgeArrow_of_injective
    (f : I → RelStructure.Embedding B C)
    (hInjective : Function.Injective
      (fun a : RelStructure.Embedding A C => actualEdge a))
    (hPhysical :
      ∀ χ : OldACarrierEdge A C → κ,
        ∃ i : I,
          ∀ a b : RelStructure.Embedding A B,
            χ (actualEdge ((f i).comp a)) =
              χ (actualEdge ((f i).comp b))) :
    ∀ ψ : RelStructure.Embedding A C → κ,
      ∃ i : I,
        ∀ a b : RelStructure.Embedding A B,
          ψ ((f i).comp a) = ψ ((f i).comp b) := by
  apply embeddingArrow_of_physicalEdgeArrow f
  · intro a b hSame
    apply hInjective
    apply Subtype.ext
    exact hSame
  · exact hPhysical

/-- In the ORDERED circulation setting, the rigidity premise is a
previously checked theorem: two finite ordered A-embeddings into a
linearly ordered host with the same image coincide. Consequently a
physical-edge F_t arrow implies the embedding arrow required by the
finite partite picture step, with no extra colour inflation. -/
theorem ordered_embeddingArrow_of_physicalEdgeArrow
    {A₀ : RelStructure L UA}
    [LinearOrder UA] [Finite UA]
    {B₀ : RelStructure L.withOrder X}
    {C₀ : RelStructure L.withOrder Y}
    (f : I → RelStructure.Embedding B₀ C₀)
    (hPhysical :
      ∀ χ : OldACarrierEdge A₀.ordered C₀ → κ,
        ∃ i : I,
          ∀ a b : RelStructure.Embedding A₀.ordered B₀,
            χ (actualEdge ((f i).comp a)) =
              χ (actualEdge ((f i).comp b))) :
    ∀ ψ : RelStructure.Embedding A₀.ordered C₀ → κ,
      ∃ i : I,
        ∀ a b : RelStructure.Embedding A₀.ordered B₀,
          ψ ((f i).comp a) = ψ ((f i).comp b) := by
  exact embeddingArrow_of_physicalEdgeArrow f
    (fun a b h => ordered_embedding_eq_of_sameCopy a b h)
    hPhysical

end StructuralRamsey.Girth.TrainRecursiveWitness

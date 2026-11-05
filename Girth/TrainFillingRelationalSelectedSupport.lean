import Girth.TrainFillingSelectedEdgeRange
import Girth.TrainFillingPrivateUniform

set_option Elab.async false

/-!
# Selected relational M-copies construct exact old physical support edges

A genuine relational embedding b : M ↪ N sends each complete carrier
of a copy of the fixed coloured edge type A in M onto the complete
carrier of its composite A-copy in N. This follows from composition of
embeddings, not from an assumed edge-map or a set-level inclusion.

When the old edge family of the uniform filling is exactly the FULL
A-support of N, this constructs an injective selected OLD physical-edge
map directly from b. The already verified filling equivalence then
constructs the corresponding selected new physical-edge embedding.

For the actual cutoff-two step, the remaining geometric identification
is that the first-wagon contractions of the heterogeneous G0 are
precisely the A-support edges of the constructed relational M. No
pruning of ambient N/H edges and no assumption of final output girth.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v

variable {L : RelLanguage.{u}} {UA W V X : Type v}

/-- Complete image of a physical source support edge is a genuine
physical support edge in the target, not just contained in one. -/
theorem supportCopy_image_mem
    (A : RelStructure L UA)
    (M : RelStructure L W) (N : RelStructure L V)
    (b : Embedding M N)
    (e : {f : Set W // f ∈ supportCopies A M}) :
    b.toFunctionEmbedding '' e.1 ∈ supportCopies A N := by
  obtain ⟨a, ha⟩ := e.2
  refine ⟨b.comp a, ?_⟩
  rw [ha]
  exact UniformPrivateTemplate.image_copyCarrier_comp A M N b a

namespace UniformFillingData

variable (U : UniformFillingData V X)

/-- The selected relational M-embedding supplies its entire old support
edge embedding, assuming the filling's actual old edge set is the FULL
coloured support of N. No independently chosen edge-map or carrier
equation is an input. -/
def selectedSupportOldEdgeEmbedding
    (A : RelStructure L UA)
    (M : RelStructure L W) (N : RelStructure L V)
    (b : Embedding M N)
    (hOld : U.oldEdges = supportCopies A N) :
    {f : Set W // f ∈ supportCopies A M} ↪ U.OldEdge :=
  U.oldEdgeEmbedding_of_exact_carriers
    (fun e : {f : Set W // f ∈ supportCopies A M} => e.1)
    (by intro e f h; exact Subtype.ext h)
    b.toFunctionEmbedding
    (fun e => (⟨b.toFunctionEmbedding '' e.1,
      by rw [hOld]; exact supportCopy_image_mem A M N b e⟩ : U.OldEdge))
    (by intro _; rfl)

/-- The constructed old physical edge carries precisely the image of
the whole source support copy. -/
@[simp] theorem selectedSupportOldEdgeEmbedding_carrier
    (A : RelStructure L UA)
    (M : RelStructure L W) (N : RelStructure L V)
    (b : Embedding M N)
    (hOld : U.oldEdges = supportCopies A N)
    (e : {f : Set W // f ∈ supportCopies A M}) :
    (U.selectedSupportOldEdgeEmbedding A M N b hOld e).1 =
      b.toFunctionEmbedding '' e.1 := rfl

/-- Exact selected filled-edge embedding, now derived from the REAL
relational M-copy and the checked edge filling equivalence. -/
noncomputable def selectedSupportFilledEdgeEmbedding
    (A : RelStructure L UA)
    (M : RelStructure L W) (N : RelStructure L V)
    (b : Embedding M N)
    (hOld : U.oldEdges = supportCopies A N) :
    ({f : Set W // f ∈ supportCopies A M} × U.TemplateEdge) ↪
      U.toTrainFilling.NewEdge :=
  U.selectedFilledEdgeEmbedding
    (U.selectedSupportOldEdgeEmbedding A M N b hOld)

end UniformFillingData
end StructuralRamsey.Girth

import Girth.ForestRelationalABCompletion
import Girth.ForestCoreACopyCoverage

/-!
# Quantified A/B completion from the actual structural local lemma

The circulation proof's forest-completion induction should depend on
the local partite lemma exactly as it is stated:
  every A-copy of the local core D lies in a designated local copy f i,
  and every bounded family of local copies is a forest.

These two local hypotheses, plus the old quantified completion property
and the standing ambient geometric invariants, suffice for the WHOLE
new quantified completion property. In particular, exact A-edge coverage
in a local gluing support is now a theorem derived from the core's
relational-copy coverage, not an additional assumption.

The remaining work is constructing the local Ramsey witness with its
declared properties and assembling the other picture-step invariants,
not repairing forest-completion bookkeeping.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- Full circulation forest-completion invariant for genuine A-support
one-edge members and transported designated B-supports, assuming only
the local structural forest/copy-covering clauses.

No independently postulated selected-piece owners or exact core-edge
preimages are required. The conclusion quantifies over ALL finite
selected families, including the empty family. -/
theorem ForestCompletionProperty.assemble_actual_AB_from_local_copy_cover
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    {K : Set (Set (RelStructure.Attachment.Vertex S
      (W := Core) (I := I)))}
    (hSourceNonempty :
      (supportCopies A (B.induce S)).Nonempty)
    (hSourceCover :
      ∀ s : S, ∃ e : Set S,
        e ∈ supportCopies A (B.induce S) ∧ s ∈ e)
    (outer : I → StrongSupportEmbedding
      (supportCopies A (B.induce S)) K)
    (hOuterCore :
      ∀ i (s : S), outer i s =
        (RelStructure.Attachment.coreEmbedding B S D f) (f i s))
    (m : ℕ)
    (hLocalForest :
      LocalForestThrough (fun i : I => (outer i).supportPiece) m)
    (hALinear :
      ALinear A (RelStructure.Attachment.attach B S D f))
    (hLocalACover :
      ∀ a : RelStructure.Embedding A D,
        ∃ i : I, copyCarrier a ⊆ copyCarrier (f i))
    (designatedOld : HypergraphPiece Old → Prop)
    (testedOld : HypergraphPiece Old → Prop)
    (hOld : ForestCompletionProperty testedOld designatedOld m)
    (hTestOldA :
      ∀ aOld : RelStructure.Embedding A B,
        testedOld (HypergraphPiece.oneEdge (copyCarrier aOld)))
    (hTestDesignated :
      ∀ T : HypergraphPiece Old, designatedOld T → testedOld T) :
    ForestCompletionProperty
      (attachedTestedABSupport A B S D f designatedOld)
      (attachedDesignatedSupport B S D f designatedOld) m := by
  have hCoreCovered :
      ∀ a : RelStructure.Embedding A
          (RelStructure.Attachment.attach B S D f),
        copyCarrier a ⊆
          Set.range (RelStructure.Attachment.coreEmbedding B S D f) →
        ∃ i : I, copyCarrier a ∈ (outer i).supportPiece.edges := by
    intro a ha
    exact attachment_core_aCopy_covered_of_local_relational_cover
      A B S D f outer hOuterCore hLocalACover a ha
  exact ForestCompletionProperty.assemble_actual_AB
    A hA B S D f
    hSourceNonempty hSourceCover outer hOuterCore
    m hLocalForest hALinear hCoreCovered
    designatedOld testedOld hOld hTestOldA hTestDesignated

end StructuralRamsey.Girth

import Girth.ForestUsedOwnerCompletion
import Girth.ForestAttachmentSupportPairs
import Girth.LinearityGirthTwo

/-!
# Circulation completion on exactly the used owners in the actual picture

This packages the genuine free-relational-attachment geometry with the
local-forest partite lemma's bounded-subfamily property. A finite NONEMPTY
selected family N chooses standard-picture owners among all local copies I.
Only the DISTINCT used owners participate in the gluing join tree, so its
finite size, surjective owner map and local forest hypothesis are automatic.

The exact pair intersections between those full standard pictures and their
small local gluing carriers are deduced from the attachment construction.
The picture's A-linearity supplies the ambient Berge girth-two input of
forest completion. The old full picture's one quantified completion
invariant supplies all local completions.

The genuinely remaining assumptions are now manifest: the existence of
the local Ramsey witness whose bounded subfamilies are forests, exact
classification of every selected A/B piece under its chosen standard
owner, gluing/standard factorization, and designated-copy transport.
The EMPTY selected family is independently complete via
emptySelected_hasForestCompletion. No global successor-history theorem
is needed in the circulation route.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Src Old Core I N : Type v}

/-- A single local-forest witness and a single old-picture completion
invariant suffice to complete any nonempty bounded selected family in
the ACTUAL free relational extension. No separately supplied forest
of used owners, owner surjectivity, or pair-intersection equality. -/
theorem ForestCompletionProperty.assemble_relational_used_owners
    [Fintype N] [Nonempty N]
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    {H : Set (Set Src)}
    {K : Set (Set (RelStructure.Attachment.Vertex S
      (W := Core) (I := I)))}
    (hSourceNonempty : H.Nonempty)
    (hSourceCover :
      ∀ x : Src, ∃ e : Set Src, e ∈ H ∧ x ∈ e)
    (outer : I → StrongSupportEmbedding H K)
    (oldFull : HypergraphPiece Old)
    (hFullCarrier : oldFull.carrier = Set.univ)
    (active : I → Src ↪ Old)
    (hFactor :
      ∀ i (x : Src), outer i x =
        relationEmbeddingToFunction
          (RelStructure.Attachment.copyEmbedding B S D f i)
          (active i x))
    (hActiveEdges :
      ∀ i (e : Set Src), e ∈ H →
        (active i) '' e ∈ oldFull.edges)
    (hAmbientEdges :
      ∀ i (e : Set Old), e ∈ oldFull.edges →
        (relationEmbeddingToFunction
          (RelStructure.Attachment.copyEmbedding B S D f i)) '' e ∈
          supportCopies A (RelStructure.Attachment.attach B S D f))
    (m : ℕ)
    (hLocalForest :
      LocalForestThrough (fun i : I => (outer i).supportPiece) m)
    (hSmallCarrier :
      ∀ i : I, (outer i).supportPiece.carrier =
        copyCarrier
          ((RelStructure.Attachment.coreEmbedding B S D f).comp (f i)))
    (hALinear :
      ALinear A (RelStructure.Attachment.attach B S D f))
    (owner : N → I)
    (hCard : Fintype.card N ≤ m)
    (selectedGlobal : N →
      HypergraphPiece
        (RelStructure.Attachment.Vertex S (W := Core) (I := I)))
    (testedOld designatedOld : HypergraphPiece Old → Prop)
    (hOld : ForestCompletionProperty testedOld designatedOld m)
    (hTestSelected :
      ∀ n : N,
        TransportedPiece testedOld
          (relationEmbeddingToFunction
            (RelStructure.Attachment.copyEmbedding B S D f (owner n)))
          (selectedGlobal n))
    (hTestActiveEdge :
      ∀ i (e : Set Src), e ∈ H →
        testedOld (HypergraphPiece.oneEdge ((active i) '' e)))
    (designated :
      HypergraphPiece
        (RelStructure.Attachment.Vertex S (W := Core) (I := I)) → Prop)
    (hDesignatedGlobal :
      ∀ i (T : HypergraphPiece Old), designatedOld T →
        designated
          (T.map (relationEmbeddingToFunction
            (RelStructure.Attachment.copyEmbedding B S D f i)))) :
    ∃ (T : UsedOwner owner → Type v),
      ∃ (finite : ∀ q, Fintype (T q)),
        letI : ∀ q, Fintype (T q) := finite
        ∃ (family : (q : UsedOwner owner) → T q →
          HypergraphPiece
            (RelStructure.Attachment.Vertex S (W := Core) (I := I))),
        ∃ keep : Finset (Sigma T),
          ForestCompletionWitness selectedGlobal designated
            (fun z : {z : Sigma T // z ∈ keep} =>
              family z.1.1 z.1.2) := by
  classical
  let standard :
      I → Old ↪ RelStructure.Attachment.Vertex S
        (W := Core) (I := I) :=
    fun i =>
      relationEmbeddingToFunction
        (RelStructure.Attachment.copyEmbedding B S D f i)
  have hPairs :
      ∀ ⦃i j : I⦄, i ≠ j →
        (oldFull.map (standard i)).carrier ∩
          (oldFull.map (standard j)).carrier =
          (outer i).supportPiece.carrier ∩
            (outer j).supportPiece.carrier :=
    attachment_full_small_support_pair_eq
      B S D f oldFull hFullCarrier
      (fun i : I => (outer i).supportPiece) hSmallCarrier
  have hGirth :
      GirthGT
        (supportCopies A (RelStructure.Attachment.attach B S D f)) 2 :=
    girthGT_two_of_aLinear A
      (RelStructure.Attachment.attach B S D f) hALinear
  exact ForestCompletionProperty.assemble_on_used_owners
    hSourceNonempty hSourceCover
    outer oldFull hFullCarrier
    standard active hFactor hActiveEdges hAmbientEdges
    m hLocalForest hPairs hGirth
    owner hCard selectedGlobal
    testedOld designatedOld hOld
    hTestSelected hTestActiveEdge
    designated hDesignatedGlobal

end StructuralRamsey.Girth

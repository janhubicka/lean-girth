import Girth.ForestFactoredStandardCompletion
import Girth.ForestAttachmentSupportPairs
import Girth.LinearityGirthTwo

/-!
# Forest-completion assembly for an actual relational picture attachment

The generic circulation completion theorem had abstract small/full support
pieces. Here the full pieces are the actual attached old picture copies,
and each small piece is required to have exactly the core image of its
designated gluing copy as carrier.

The exact pairwise intersection hypothesis is no longer passed independently:
it is a theorem about the free relational attachment. The ambient girth-two
hypothesis is also no longer independent: A-linearity of the attached
picture supplies it.

Together with factorized gluing maps and the old complete support piece,
this obtains a finite completed forest using the ONE old-picture completion
invariant. Remaining premises are precisely the genuine local forest witness,
support-edge/selected-piece ownership, factorization of the actual gluing
maps and global designated-copy transport.

This is a conditional picture-step theorem, not yet a proof of the full
manuscript preservation proposition.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Src Old Core Q N : Type v}

/-- The existing circulation two-carrier forest-completion assembly applied
to the ACTUAL free-attached picture. The full-standard picture carriers and
their pair intersections are derived from the free attachment itself;
A-linearity supplies the needed ambient Berge girth bound. -/
theorem ForestCompletionProperty.assemble_relational_attachment
    [Fintype Q] [Nonempty Q] [DecidableEq Q] [Fintype N]
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : Q → RelStructure.Embedding (B.induce S) D)
    {H : Set (Set Src)}
    {K : Set (Set (RelStructure.Attachment.Vertex S
      (W := Core) (I := Q)))}
    (hSourceNonempty : H.Nonempty)
    (hSourceCover :
      ∀ x : Src, ∃ e : Set Src, e ∈ H ∧ x ∈ e)
    (outer : Q → StrongSupportEmbedding H K)
    (oldFull : HypergraphPiece Old)
    (hFullCarrier : oldFull.carrier = Set.univ)
    (active : Q → Src ↪ Old)
    (hFactor :
      ∀ q (x : Src), outer q x =
        relationEmbeddingToFunction
          (RelStructure.Attachment.copyEmbedding B S D f q)
          (active q x))
    (hActiveEdges :
      ∀ q (e : Set Src), e ∈ H →
        (active q) '' e ∈ oldFull.edges)
    (hAmbientEdges :
      ∀ q (e : Set Old), e ∈ oldFull.edges →
        (relationEmbeddingToFunction
          (RelStructure.Attachment.copyEmbedding B S D f q)) '' e ∈
          supportCopies A (RelStructure.Attachment.attach B S D f))
    (hInnerForest :
      ForestOfCopies (fun q : Q => (outer q).supportPiece))
    (hSmallCarrier :
      ∀ q : Q, (outer q).supportPiece.carrier =
        copyCarrier
          ((RelStructure.Attachment.coreEmbedding B S D f).comp (f q)))
    (hALinear :
      ALinear A (RelStructure.Attachment.attach B S D f))
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (m : ℕ)
    (hCard : Fintype.card N ≤ m)
    (selectedGlobal : N →
      HypergraphPiece
        (RelStructure.Attachment.Vertex S (W := Core) (I := Q)))
    (testedOld designatedOld : HypergraphPiece Old → Prop)
    (hOld : ForestCompletionProperty testedOld designatedOld m)
    (hTestSelected :
      ∀ n : N,
        TransportedPiece testedOld
          (relationEmbeddingToFunction
            (RelStructure.Attachment.copyEmbedding B S D f (owner n)))
          (selectedGlobal n))
    (hTestActiveEdge :
      ∀ q (e : Set Src), e ∈ H →
        testedOld (HypergraphPiece.oneEdge ((active q) '' e)))
    (designated :
      HypergraphPiece
        (RelStructure.Attachment.Vertex S (W := Core) (I := Q)) → Prop)
    (hDesignatedGlobal :
      ∀ q (T : HypergraphPiece Old), designatedOld T →
        designated
          (T.map (relationEmbeddingToFunction
            (RelStructure.Attachment.copyEmbedding B S D f q)))) :
    ∃ (T : Q → Type v),
      ∃ (finite : ∀ q, Fintype (T q)),
        letI : ∀ q, Fintype (T q) := finite
        ∃ (family : (q : Q) → T q →
          HypergraphPiece
            (RelStructure.Attachment.Vertex S (W := Core) (I := Q))),
        ∃ keep : Finset (Sigma T),
          ForestCompletionWitness selectedGlobal designated
            (fun z : {z : Sigma T // z ∈ keep} =>
              family z.1.1 z.1.2) := by
  classical
  let standard :
      Q → Old ↪ RelStructure.Attachment.Vertex S
        (W := Core) (I := Q) :=
    fun q =>
      relationEmbeddingToFunction
        (RelStructure.Attachment.copyEmbedding B S D f q)
  have hPair :
      ∀ ⦃q r : Q⦄, q ≠ r →
        (oldFull.map (standard q)).carrier ∩
          (oldFull.map (standard r)).carrier =
          (outer q).supportPiece.carrier ∩
            (outer r).supportPiece.carrier := by
    exact attachment_full_small_support_pair_eq
      B S D f oldFull hFullCarrier
      (fun q : Q => (outer q).supportPiece) hSmallCarrier
  have hAmbientGirth :
      GirthGT
        (supportCopies A (RelStructure.Attachment.attach B S D f)) 2 :=
    girthGT_two_of_aLinear A
      (RelStructure.Attachment.attach B S D f) hALinear
  exact ForestCompletionProperty.assemble_factored_full_standards
    hSourceNonempty hSourceCover outer oldFull hFullCarrier
    standard active hFactor hActiveEdges hAmbientEdges
    hInnerForest hPair hAmbientGirth
    owner hSurj m hCard selectedGlobal
    testedOld designatedOld hOld hTestSelected
    hTestActiveEdge designated hDesignatedGlobal

end StructuralRamsey.Girth

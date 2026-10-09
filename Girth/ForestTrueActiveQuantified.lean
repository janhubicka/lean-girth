import Girth.ForestTrueActiveCompletion

/-!
# Fully quantified forest completion at the actual partite attachment

The circulation preservation property is quantified over EVERY finite
selection of tested A/B support pieces, including the empty selection.
Its nonempty case should not require a separately chosen local forest
for each particular selection: the local partite Ramsey witness supplies
foresthood for all bounded subfamilies, and the used-owner image performs
the indexing and cardinal bookkeeping.

The theorem below packages the full universal quantifiers and extracts
one proper ForestCompletionWitness for each selected family. The only
nonstructural step left as an explicit hypothesis is the honest
selected-piece OWNERSHIP statement: every tested new A/B-piece has an
old tested support preimage in some standard picture.

This is still a conditional component of certpres. In particular we do
not assume or pretend to have formalized the existence of the local
Ramsey witness, the complete active support identification, or all
four simultaneous picture induction invariants.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- Full finite-family forest completion of the actual attached
picture. All selection, owner, finiteness, empty-family and
forest-assembly quantifiers are discharged; the ownership
classification of actual new tested A/B pieces remains a transparent
hypothesis.

Only a single old-picture completion invariant is used. -/
theorem ForestCompletionProperty.assemble_true_active_quantified
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    {H : Set (Set S)}
    {K : Set (Set (RelStructure.Attachment.Vertex S
      (W := Core) (I := I)))}
    (hSourceNonempty : H.Nonempty)
    (hSourceCover :
      ∀ s : S, ∃ e : Set S, e ∈ H ∧ s ∈ e)
    (outer : I → StrongSupportEmbedding H K)
    (hOuterCore :
      ∀ i (s : S), outer i s =
        (RelStructure.Attachment.coreEmbedding B S D f) (f i s))
    (oldFull : HypergraphPiece Old)
    (hFullCarrier : oldFull.carrier = Set.univ)
    (hActiveEdges :
      ∀ e : Set S, e ∈ H →
        Subtype.val '' e ∈ oldFull.edges)
    (hAmbientEdges :
      ∀ i (e : Set Old), e ∈ oldFull.edges →
        (relationEmbeddingToFunction
          (RelStructure.Attachment.copyEmbedding B S D f i)) '' e ∈
          supportCopies A (RelStructure.Attachment.attach B S D f))
    (m : ℕ)
    (hLocalForest :
      LocalForestThrough (fun i : I => (outer i).supportPiece) m)
    (hALinear :
      ALinear A (RelStructure.Attachment.attach B S D f))
    (testedOld designatedOld : HypergraphPiece Old → Prop)
    (hOld : ForestCompletionProperty testedOld designatedOld m)
    (hTestActiveEdge :
      ∀ e : Set S, e ∈ H →
        testedOld (HypergraphPiece.oneEdge (Subtype.val '' e)))
    (testedNew designatedNew :
      HypergraphPiece
        (RelStructure.Attachment.Vertex S (W := Core) (I := I)) → Prop)
    (hChooseOwner :
      ∀ (N : Type v) [Fintype N]
        (selected : N → HypergraphPiece
          (RelStructure.Attachment.Vertex S (W := Core) (I := I))),
        (∀ n, testedNew (selected n)) →
        Fintype.card N ≤ m →
          ∃ owner : N → I,
            ∀ n : N, TransportedPiece testedOld
              (relationEmbeddingToFunction
                (RelStructure.Attachment.copyEmbedding B S D f (owner n)))
              (selected n))
    (hDesignatedGlobal :
      ∀ i (T : HypergraphPiece Old), designatedOld T →
        designatedNew
          (T.map (relationEmbeddingToFunction
            (RelStructure.Attachment.copyEmbedding B S D f i)))) :
    ForestCompletionProperty testedNew designatedNew m := by
  classical
  intro N inst selected hTest hCard
  by_cases hN : Nonempty N
  · letI : Nonempty N := hN
    obtain ⟨owner, hSelected⟩ :=
      hChooseOwner N selected hTest hCard
    obtain ⟨T, finite, family, keep, hWitness⟩ :=
      ForestCompletionProperty.assemble_true_active_used_owners
        A B S D f hSourceNonempty hSourceCover
        outer hOuterCore oldFull hFullCarrier
        hActiveEdges hAmbientEdges
        m hLocalForest hALinear owner hCard selected
        testedOld designatedOld hOld hSelected hTestActiveEdge
        designatedNew hDesignatedGlobal
    letI : Fintype (UsedOwner owner) := usedOwnerFintype owner
    letI : ∀ q : UsedOwner owner, Fintype (T q) := finite
    refine ⟨{z : Sigma T // z ∈ keep}, ?_, ?_⟩
    · infer_instance
    · exact ⟨(fun z => family z.1.1 z.1.2), hWitness⟩
  · letI : IsEmpty N := ⟨fun n => hN ⟨n⟩⟩
    obtain ⟨T, finite, completed, hWitness⟩ :=
      emptySelected_hasForestCompletion selected designatedNew
    exact ⟨T, finite, completed, hWitness⟩

end StructuralRamsey.Girth

import Girth.ForestRelationalUsedOwnerCompletion

/-!
# The actual active-subsystem inclusion supplies standard-copy factorization

For the true old active vertex set S, the corresponding source type is
the subtype S and the active inclusion is simply Subtype.val : S ↪ Old.
The relational attachment equation copy_extends already proves that
the gluing image of a point s:S in the core equals the full standard
copy of its old vertex s.val.

Consequently a local strong-support map whose underlying function is
exactly the core gluing embedding factors automatically through the full
standard copy. The old active support-edge and tested one-edge hypotheses
then have no owner dependence. The other inputs of the completed-forest
invariant remain those of the genuine local Ramsey witness and its
selected A/B-copy classification.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I N : Type v}

/-- The concrete relation between the core image of the old active part
and its image inside one fresh full standard picture. This is the
equation already used implicitly throughout the circulation proof. -/
theorem attachment_core_gluing_eq_standard
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I) (s : S) :
    (RelStructure.Attachment.coreEmbedding B S D f) (f i s) =
      (RelStructure.Attachment.copyEmbedding B S D f i) s.1 :=
  (RelStructure.Attachment.copy_extends B S D f i s).symm

/-- Completion on the genuine active subtype. The standard-copy
factorization and all per-owner active-inclusion identities are
derived from attachment_core_gluing_eq_standard, not assumed.

As before, the finite selected family is nonempty here; an empty
selection is completed by emptySelected_hasForestCompletion. -/
theorem ForestCompletionProperty.assemble_true_active_used_owners
    [Fintype N] [Nonempty N]
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
      ∀ e : Set S, e ∈ H →
        testedOld (HypergraphPiece.oneEdge (Subtype.val '' e)))
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
  let activeInclusion : S ↪ Old :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hFactor :
      ∀ i (s : S), outer i s =
        relationEmbeddingToFunction
          (RelStructure.Attachment.copyEmbedding B S D f i)
          (activeInclusion s) := by
    intro i s
    calc
      outer i s =
          (RelStructure.Attachment.coreEmbedding B S D f) (f i s) :=
        hOuterCore i s
      _ = (RelStructure.Attachment.copyEmbedding B S D f i) s.1 :=
        attachment_core_gluing_eq_standard B S D f i s
      _ = relationEmbeddingToFunction
          (RelStructure.Attachment.copyEmbedding B S D f i)
          (activeInclusion s) := rfl
  exact ForestCompletionProperty.assemble_relational_used_owners
    A B S D f
    hSourceNonempty hSourceCover
    outer oldFull hFullCarrier
    (fun _ : I => activeInclusion)
    hFactor
    (fun _ e he => hActiveEdges e he)
    hAmbientEdges m hLocalForest hSmallCarrier hALinear
    owner hCard selectedGlobal testedOld designatedOld
    hOld hTestSelected (fun _ e he => hTestActiveEdge e he)
    designated hDesignatedGlobal

end StructuralRamsey.Girth

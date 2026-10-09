import Girth.ForestSelectedPieceTransport
import Girth.DesignatedAttachment

/-!
# Actual A-copy ownership in a free relational picture attachment

There is a geometric distinction between the full standard copies of
the old picture and the small gluing copies inside the new core.
An A-copy in the attached picture either lives in the core or in
one full standard copy, by irreducibility of A and free attachment.

For an A-copy in a standard picture, its *whole one-edge support piece*
is exactly the image of a genuine old A-copy; carrier containment alone
is not used as a substitute for transport. In the core, the local
support-cover property supplies a designated gluing A-edge, whose
preimage is already handled by strong-support factorization.

Consequently the A-side of the selected-piece ownership condition can
be discharged from precisely these geometric facts. Designated B-piece
transport and the existence of the local Ramsey witness are separate
remaining steps of the circulation proof.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I Src : Type v}

/-- A copy of an irreducible A in a free relational attachment is
wholly in the core or wholly in one full standard copy. No assumption
that the entire attached picture is a disjoint union is made. -/
theorem attachment_aCopy_core_or_standard
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (a : RelStructure.Embedding A (RelStructure.Attachment.attach B S D f)) :
    (∀ u : UA, ∃ y : Core,
      a u = (RelStructure.Attachment.coreEmbedding B S D f) y) ∨
    (∃ i : I, ∀ u : UA, ∃ x : Old,
      a u = (RelStructure.Attachment.copyEmbedding B S D f i) x) := by
  let T : Set (RelStructure.Attachment.Vertex S (W := Core) (I := I)) :=
    copyCarrier a
  have hT :
      ((RelStructure.Attachment.attach B S D f).induce T).Irreducible :=
    hA.range_embedding a
  have hsplit :=
    RelStructure.Attachment.irreducible_core_or_copy
      (B := B) (S := S) (D := D) (f := f) T hT
  rcases hsplit with hCore | ⟨i, hCopy⟩
  · left
    intro u
    exact hCore ⟨a u, ⟨u, rfl⟩⟩
  · right
    refine ⟨i, ?_⟩
    intro u
    exact hCopy ⟨a u, ⟨u, rfl⟩⟩

/-- If an A-copy of the attached picture lies in one full standard
picture, its one-edge support piece has an EXACT tested old A-copy
preimage, not merely a containing old carrier. -/
theorem attached_standard_aCopy_transported
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I)
    (a : RelStructure.Embedding A (RelStructure.Attachment.attach B S D f))
    (hInside : ∀ u : UA, ∃ x : Old,
      a u = (RelStructure.Attachment.copyEmbedding B S D f i) x)
    (testedOld : HypergraphPiece Old → Prop)
    (hTestA : ∀ aOld : RelStructure.Embedding A B,
      testedOld (HypergraphPiece.oneEdge (copyCarrier aOld))) :
    TransportedPiece testedOld
      (relationEmbeddingToFunction
        (RelStructure.Attachment.copyEmbedding B S D f i))
      (HypergraphPiece.oneEdge (copyCarrier a)) := by
  classical
  let std : RelStructure.Embedding B
      (RelStructure.Attachment.attach B S D f) :=
    RelStructure.Attachment.copyEmbedding B S D f i
  let aOld : RelStructure.Embedding A B :=
    a.factorThroughRange std hInside
  have hSpec (u : UA) : a u = std (aOld u) :=
    Classical.choose_spec (hInside u)
  let φ := relationEmbeddingToFunction std
  have hCarrier :
      copyCarrier a = φ '' copyCarrier aOld := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨aOld u, ⟨u, rfl⟩, ?_⟩
      exact (hSpec u).symm
    · rintro ⟨x, ⟨u, rfl⟩, hx⟩
      exact ⟨u, (hSpec u).trans hx⟩
  refine ⟨HypergraphPiece.oneEdge (copyCarrier aOld),
    hTestA aOld, ?_⟩
  rw [HypergraphPiece.oneEdge_map]
  exact congrArg HypergraphPiece.oneEdge hCarrier

/-- The A-copy ownership classification required by circulation
completion: every actual A-copy is either a local core edge with a
tested old active A-edge preimage, or a tested old A-copy transported
into its containing full standard picture.

The only genuinely local new input is that every core A-copy edge
belongs to some designated gluing support piece. The full-standard
case and its exact one-edge preimage are proved unconditionally. -/
theorem attached_aCopy_has_tested_standard_owner
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    {H : Set (Set Src)}
    {K : Set (Set (RelStructure.Attachment.Vertex S
      (W := Core) (I := I)))}
    (outer : I → StrongSupportEmbedding H K)
    (active : I → Src ↪ Old)
    (hFactor :
      ∀ i (x : Src), outer i x =
        (RelStructure.Attachment.copyEmbedding B S D f i) (active i x))
    (testedOld : HypergraphPiece Old → Prop)
    (hTestA :
      ∀ aOld : RelStructure.Embedding A B,
        testedOld (HypergraphPiece.oneEdge (copyCarrier aOld)))
    (hTestActiveEdge :
      ∀ i (e : Set Src), e ∈ H →
        testedOld (HypergraphPiece.oneEdge ((active i) '' e)))
    (hCoreCovered :
      ∀ a : RelStructure.Embedding A
          (RelStructure.Attachment.attach B S D f),
        copyCarrier a ⊆
          Set.range (RelStructure.Attachment.coreEmbedding B S D f) →
        ∃ i : I, copyCarrier a ∈ (outer i).supportPiece.edges)
    (a : RelStructure.Embedding A (RelStructure.Attachment.attach B S D f)) :
    ∃ i : I,
      TransportedPiece testedOld
        (relationEmbeddingToFunction
          (RelStructure.Attachment.copyEmbedding B S D f i))
        (HypergraphPiece.oneEdge (copyCarrier a)) := by
  rcases attachment_aCopy_core_or_standard A hA B S D f a with
    hCore | ⟨i, hStandard⟩
  · have hInsideCore :
        copyCarrier a ⊆
          Set.range (RelStructure.Attachment.coreEmbedding B S D f) := by
      rintro z ⟨u, rfl⟩
      obtain ⟨y, hy⟩ := hCore u
      exact ⟨y, hy.symm⟩
    obtain ⟨i, he⟩ := hCoreCovered a hInsideCore
    refine ⟨i, ?_⟩
    exact (outer i).oneEdge_transported_of_factor
      (active i)
      (relationEmbeddingToFunction
        (RelStructure.Attachment.copyEmbedding B S D f i))
      (hFactor i) testedOld (hTestActiveEdge i)
      (copyCarrier a) he
  · exact ⟨i, attached_standard_aCopy_transported
      A B S D f i a hStandard testedOld hTestA⟩

end StructuralRamsey.Girth

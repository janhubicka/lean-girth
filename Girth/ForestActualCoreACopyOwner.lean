import Girth.ForestActualACopyOwner
import Girth.LocalForestPieces

/-!
# Exact coverage of ambient core A-copies by local witness edges

The local-forest partite witness explicitly covers every A-support edge
of its relational core by a designated local copy.  In the actual free
attachment, an ambient A-copy whose entire carrier is in the core
factors through the core embedding as an old A-copy of the local witness.

Combining these facts, it is an exact edge of a gluing-copy support piece.
This discharges the remaining core-edge clause of the actual A-copy owner
theorem, rather than postulating it separately.

The full local Ramsey witness's existence is still a separate theorem:
this file consumes its exact A-support and edge-cover properties, not an
unproved global Ramsey arrow.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I Src : Type v}

/-- Every core-contained A-copy of the actual attached structure is
an exact A-edge of some local designated gluing-copy support piece.

We assume only that the core support of A is exactly the declared local
edge family K and that every edge of K is in the image of some designated
strong-support copy. -/
theorem attached_core_aCopy_in_local_supportPiece
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    {H : Set (Set Src)}
    {K : Set (Set Core)}
    (localCopy : I → StrongSupportEmbedding H K)
    (hLocalEdgeCover :
      ∀ e : Set Core, e ∈ K →
        ∃ i : I, ∃ e₀ : Set Src, e₀ ∈ H ∧
          e = (localCopy i) '' e₀)
    (hCoreSupport : supportCopies A D = K)
    {KWhole : Set (Set (RelStructure.Attachment.Vertex S
      (W := Core) (I := I)))}
    (outer : I → StrongSupportEmbedding H KWhole)
    (hOuterCore :
      ∀ i (x : Src), outer i x =
        (RelStructure.Attachment.coreEmbedding B S D f) (localCopy i x))
    (a : RelStructure.Embedding A (RelStructure.Attachment.attach B S D f))
    (hInside :
      copyCarrier a ⊆
        Set.range (RelStructure.Attachment.coreEmbedding B S D f)) :
    ∃ i : I, copyCarrier a ∈ (outer i).supportPiece.edges := by
  classical
  let core : RelStructure.Embedding D
      (RelStructure.Attachment.attach B S D f) :=
    RelStructure.Attachment.coreEmbedding B S D f
  have hFactorA :
      ∀ u : UA, ∃ x : Core, a u = core x := by
    intro u
    exact hInside ⟨u, rfl⟩
  let aCore : RelStructure.Embedding A D :=
    a.factorThroughRange core hFactorA
  have hSpec (u : UA) : a u = core (aCore u) :=
    Classical.choose_spec (hFactorA u)
  have hCarrier :
      copyCarrier a = core '' copyCarrier aCore := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨aCore u, ⟨u, rfl⟩, (hSpec u).symm⟩
    · rintro ⟨x, ⟨u, rfl⟩, hx⟩
      exact ⟨u, (hSpec u).trans hx⟩
  have heK : copyCarrier aCore ∈ K := by
    rw [← hCoreSupport]
    exact ⟨aCore, rfl⟩
  obtain ⟨i, e₀, he₀, heq⟩ :=
    hLocalEdgeCover (copyCarrier aCore) heK
  have hImages :
      core '' ((localCopy i) '' e₀) = (outer i) '' e₀ := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, hxy⟩, hyz⟩
      refine ⟨x, hx, ?_⟩
      calc
        outer i x = core (localCopy i x) := hOuterCore i x
        _ = core y := congrArg core hxy
        _ = z := hyz
    · rintro ⟨x, hx, hxz⟩
      refine ⟨localCopy i x, ⟨x, hx, rfl⟩, ?_⟩
      calc
        core (localCopy i x) = outer i x := (hOuterCore i x).symm
        _ = z := hxz
  have hEdge :
      copyCarrier a = (outer i) '' e₀ := by
    calc
      copyCarrier a = core '' copyCarrier aCore := hCarrier
      _ = core '' ((localCopy i) '' e₀) :=
        congrArg (fun U : Set Core => core '' U) heq
      _ = (outer i) '' e₀ := hImages
  exact ⟨i, ⟨e₀, he₀, hEdge⟩⟩

/-- Every ambient A-copy in the actual free attachment admits an exact
tested old A-support preimage in a standard picture, provided the local
decorated Ramsey witness covers its core support edges.

The standard-picture case needs no local-forest property. The core case
uses only support equality, designated gluing edge coverage, and the
actual gluing factorization. -/
theorem attached_aCopy_tested_owner_of_local_edge_cover
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    {H : Set (Set Src)} {K : Set (Set Core)}
    (localCopy : I → StrongSupportEmbedding H K)
    (hLocalEdgeCover :
      ∀ e : Set Core, e ∈ K →
        ∃ i : I, ∃ e₀ : Set Src, e₀ ∈ H ∧
          e = (localCopy i) '' e₀)
    (hCoreSupport : supportCopies A D = K)
    {KWhole : Set (Set (RelStructure.Attachment.Vertex S
      (W := Core) (I := I)))}
    (outer : I → StrongSupportEmbedding H KWhole)
    (hOuterCore :
      ∀ i (x : Src), outer i x =
        (RelStructure.Attachment.coreEmbedding B S D f) (localCopy i x))
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
    (a : RelStructure.Embedding A (RelStructure.Attachment.attach B S D f)) :
    ∃ i : I, TransportedPiece testedOld
      (relationEmbeddingToFunction
        (RelStructure.Attachment.copyEmbedding B S D f i))
      (HypergraphPiece.oneEdge (copyCarrier a)) := by
  exact attached_aCopy_has_tested_standard_owner
    A hA B S D f outer active hFactor
    testedOld hTestA hTestActiveEdge
    (fun aCore hInside =>
      attached_core_aCopy_in_local_supportPiece
        A B S D f localCopy hLocalEdgeCover hCoreSupport
        outer hOuterCore aCore hInside) a

end StructuralRamsey.Girth

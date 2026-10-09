import Girth.ForestActualACopyOwner
import Girth.ForestTrueActiveCompletion

/-!
# Exact core A-edge coverage from local relational A-copy coverage

The structural local-forest partite lemma says that every A-copy of
the local core D lies in some designated embedded copy f i of the old
active subsystem B.induce S. For the circulation completion proof, it
is tempting to assume the stronger statement that the image of each
such core A-copy is literally an edge of the corresponding strong
support piece. This does not have to be a new hypothesis.

Because f i is a RELATIONAL embedding, a core A-embedding whose carrier
is contained in the image of f i factors as an actual A-embedding into
B.induce S. Its whole support edge transports through
the actual core gluing map, so the exact edge equality follows.

There is no use of any blanket foresthood assumption and no
replacement of image-edge equality by mere carrier inclusion.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- Structural local-copy containment implies exact A-edge support
coverage in the full attachment core. The old active source support is
exactly the support of A in B.induce S; K need not be all ambient edges. -/
theorem attachment_core_aCopy_covered_of_local_relational_cover
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    {K : Set (Set (RelStructure.Attachment.Vertex S
      (W := Core) (I := I)))}
    (outer : I → StrongSupportEmbedding
      (supportCopies A (B.induce S)) K)
    (hOuterCore :
      ∀ i (s : S), outer i s =
        (RelStructure.Attachment.coreEmbedding B S D f) (f i s))
    (hLocalCover :
      ∀ a : RelStructure.Embedding A D,
        ∃ i : I, copyCarrier a ⊆ copyCarrier (f i))
    (a : RelStructure.Embedding A
      (RelStructure.Attachment.attach B S D f))
    (hCore :
      copyCarrier a ⊆
        Set.range (RelStructure.Attachment.coreEmbedding B S D f)) :
    ∃ i : I, copyCarrier a ∈ (outer i).supportPiece.edges := by
  classical
  let core : RelStructure.Embedding D
      (RelStructure.Attachment.attach B S D f) :=
    RelStructure.Attachment.coreEmbedding B S D f
  have hFactorCore :
      ∀ u : UA, ∃ y : Core, a u = core y := by
    intro u
    exact hCore ⟨u, rfl⟩
  let aCore : RelStructure.Embedding A D :=
    a.factorThroughRange core hFactorCore
  have hCoreSpec (u : UA) : a u = core (aCore u) :=
    Classical.choose_spec (hFactorCore u)
  obtain ⟨i, hLocal⟩ := hLocalCover aCore
  have hFactorLocal :
      ∀ u : UA, ∃ s : S, aCore u = f i s := by
    intro u
    exact hLocal ⟨u, rfl⟩
  let aActive : RelStructure.Embedding A (B.induce S) :=
    aCore.factorThroughRange (f i) hFactorLocal
  have hLocalSpec (u : UA) :
      aCore u = f i (aActive u) :=
    Classical.choose_spec (hFactorLocal u)
  have hEq (u : UA) :
      a u = outer i (aActive u) := by
    calc
      a u = core (aCore u) := hCoreSpec u
      _ = core (f i (aActive u)) := congrArg core (hLocalSpec u)
      _ = outer i (aActive u) := (hOuterCore i (aActive u)).symm
  have hEdge : copyCarrier aActive ∈
      supportCopies A (B.induce S) := ⟨aActive, rfl⟩
  have hCarrier :
      copyCarrier a = outer i '' copyCarrier aActive := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨aActive u, ⟨u, rfl⟩, (hEq u).symm⟩
    · rintro ⟨s, ⟨u, rfl⟩, hz⟩
      exact ⟨u, (hEq u).trans hz⟩
  exact ⟨i, copyCarrier aActive, hEdge, hCarrier⟩

end StructuralRamsey.Girth

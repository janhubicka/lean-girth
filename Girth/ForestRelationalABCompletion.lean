import Girth.ForestTrueActiveQuantified
import Girth.ForestActualACopyOwner

/-!
# The quantified circulation completion for actual A/B support members

The manuscript tests precisely:
* one-edge support pieces of ambient A-embeddings; and
* chosen designated B-support pieces, transported from old designated
  B-members through a full standard old-picture embedding.

For those explicit two types of members, the owner-selection premise
of assemble_true_active_quantified is NOT independent. Every A-copy
either belongs to one full standard picture or lies in the local core,
and the latter is covered by a designated local gluing A-edge.
Every designated B-support already comes with a chosen old B-support
and standard-copy index.

This file derives exact image equality for source and old A-support
edges, so full support-piece transport is used throughout. It leaves
the *actual* structural local-forest witness (including core A-edge
coverage and bounded forests), as well as the full picture induction,
to the separate local-forest and certpres arguments.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- The old complete A-support piece, with all its vertices and exactly
the support edges of actual old A-copies. -/
def fullASupportPiece
    (A : RelStructure L UA) (B : RelStructure L Old) :
    HypergraphPiece Old where
  carrier := Set.univ
  edges := supportCopies A B
  edge_subset_carrier := by
    intro e he x hx
    trivial

@[simp] theorem fullASupportPiece_carrier
    (A : RelStructure L UA) (B : RelStructure L Old) :
    (fullASupportPiece A B).carrier = Set.univ := rfl

@[simp] theorem fullASupportPiece_edges
    (A : RelStructure L UA) (B : RelStructure L Old) :
    (fullASupportPiece A B).edges = supportCopies A B := rfl

/-- Under a relational embedding, the whole image of an actual A-edge
is again an actual ambient A-edge. -/
theorem aSupport_image_of_embedding
    (A : RelStructure L UA)
    {W : Type v}
    (B : RelStructure L Old)
    (C : RelStructure L W)
    (std : RelStructure.Embedding B C)
    {e : Set Old}
    (he : e ∈ supportCopies A B) :
    (relationEmbeddingToFunction std) '' e ∈ supportCopies A C := by
  rcases he with ⟨a, rfl⟩
  refine ⟨std.comp a, ?_⟩
  change (relationEmbeddingToFunction std) '' Set.range a =
    Set.range (std.comp a)
  ext z
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨a u, ⟨u, rfl⟩, rfl⟩

/-- The support edges of the active induced old subsystem include into
the entire old A-support; this is exact image transport, not an
assumption on unrelated hyperedges. -/
theorem activeASupport_image_in_old
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    {e : Set S}
    (he : e ∈ supportCopies A (B.induce S)) :
    Subtype.val '' e ∈ supportCopies A B := by
  have h := aSupport_image_of_embedding A (B.induce S) B
    (RelStructure.inclusion B S) he
  exact h

/-- The designated pieces of the new attachment are precisely old
designated supports transported by one standard-copy embedding. -/
def attachedDesignatedSupport
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (designatedOld : HypergraphPiece Old → Prop)
    (T : HypergraphPiece
      (RelStructure.Attachment.Vertex S (W := Core) (I := I))) : Prop :=
  ∃ (i : I) (R : HypergraphPiece Old),
    designatedOld R ∧
      T = R.map (relationEmbeddingToFunction
        (RelStructure.Attachment.copyEmbedding B S D f i))

/-- The exact A/B support-piece class tested by the forest-completion
invariant. Old designated members are deliberately not confused with
ALL ambient copies of B until irreducible coverage proves coincidence. -/
def attachedTestedABSupport
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (designatedOld : HypergraphPiece Old → Prop)
    (T : HypergraphPiece
      (RelStructure.Attachment.Vertex S (W := Core) (I := I))) : Prop :=
  (∃ a : RelStructure.Embedding A
      (RelStructure.Attachment.attach B S D f),
    T = HypergraphPiece.oneEdge (copyCarrier a)) ∨
  attachedDesignatedSupport B S D f designatedOld T

/-- The actual selected A/B support pieces satisfy the ENTIRE
quantified completion property. Local witness existence is represented
by its true two geometric consequences: bounded local-copy forests
and coverage of all core A-edges by local gluing support pieces.

There is NO independent finite-family owner-selection assumption:
A-owners are constructed from irreducibility, free attachment and core
edge coverage; designated B-owners are their defining transport labels. -/
theorem ForestCompletionProperty.assemble_actual_AB
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
    (hCoreCovered :
      ∀ a : RelStructure.Embedding A
        (RelStructure.Attachment.attach B S D f),
        copyCarrier a ⊆
          Set.range (RelStructure.Attachment.coreEmbedding B S D f) →
        ∃ i : I, copyCarrier a ∈ (outer i).supportPiece.edges)
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
  classical
  let full := fullASupportPiece A B
  have hFull : full.carrier = Set.univ := rfl
  have hActiveEdges :
      ∀ e : Set S, e ∈ supportCopies A (B.induce S) →
        Subtype.val '' e ∈ full.edges := by
    intro e he
    exact activeASupport_image_in_old A B S he
  have hAmbientEdges :
      ∀ i (e : Set Old), e ∈ full.edges →
        (relationEmbeddingToFunction
          (RelStructure.Attachment.copyEmbedding B S D f i)) '' e ∈
            supportCopies A (RelStructure.Attachment.attach B S D f) := by
    intro i e he
    exact aSupport_image_of_embedding A B
      (RelStructure.Attachment.attach B S D f)
      (RelStructure.Attachment.copyEmbedding B S D f i) he
  have hTestActiveEdge :
      ∀ e : Set S, e ∈ supportCopies A (B.induce S) →
        testedOld (HypergraphPiece.oneEdge (Subtype.val '' e)) := by
    intro e he
    rcases he with ⟨a, rfl⟩
    let aOld : RelStructure.Embedding A B :=
      (RelStructure.inclusion B S).comp a
    have hEq :
        Subtype.val '' copyCarrier a = copyCarrier aOld := by
      ext z
      constructor
      · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
        exact ⟨u, rfl⟩
      · rintro ⟨u, rfl⟩
        exact ⟨a u, ⟨u, rfl⟩, rfl⟩
    rw [hEq]
    exact hTestOldA aOld
  have hFactor :
      ∀ i (s : S), outer i s =
        (RelStructure.Attachment.copyEmbedding B S D f i) s.1 := by
    intro i s
    calc
      outer i s =
          (RelStructure.Attachment.coreEmbedding B S D f) (f i s) :=
        hOuterCore i s
      _ = (RelStructure.Attachment.copyEmbedding B S D f i) s.1 :=
        attachment_core_gluing_eq_standard B S D f i s
  let active : I → S ↪ Old :=
    fun _ => ⟨Subtype.val, Subtype.val_injective⟩
  have hAOwner :
      ∀ a : RelStructure.Embedding A
        (RelStructure.Attachment.attach B S D f),
      ∃ i : I,
        TransportedPiece testedOld
          (relationEmbeddingToFunction
            (RelStructure.Attachment.copyEmbedding B S D f i))
          (HypergraphPiece.oneEdge (copyCarrier a)) := by
    intro a
    exact attached_aCopy_has_tested_standard_owner
      A hA B S D f outer active hFactor
      testedOld hTestOldA
      (fun _ e he => hTestActiveEdge e he)
      hCoreCovered a
  have hPointOwner :
      ∀ T : HypergraphPiece
        (RelStructure.Attachment.Vertex S (W := Core) (I := I)),
        attachedTestedABSupport A B S D f designatedOld T →
        ∃ i : I,
          TransportedPiece testedOld
            (relationEmbeddingToFunction
              (RelStructure.Attachment.copyEmbedding B S D f i)) T := by
    intro T hTest
    rcases hTest with ⟨a, ha⟩ | ⟨i, R, hR, hEq⟩
    · rw [ha]
      exact hAOwner a
    · refine ⟨i, R, hTestDesignated R hR, hEq⟩
  have hChooseOwner :
      ∀ (N : Type v) [Fintype N]
        (selected : N → HypergraphPiece
          (RelStructure.Attachment.Vertex S (W := Core) (I := I))),
        (∀ n, attachedTestedABSupport A B S D f
          designatedOld (selected n)) →
        Fintype.card N ≤ m →
          ∃ owner : N → I,
            ∀ n : N,
              TransportedPiece testedOld
                (relationEmbeddingToFunction
                  (RelStructure.Attachment.copyEmbedding B S D f (owner n)))
                (selected n) := by
    intro N _ selected hSelected _
    have hExist (n : N) := hPointOwner (selected n) (hSelected n)
    choose owner hOwner using hExist
    exact ⟨owner, hOwner⟩
  have hDesignatedGlobal :
      ∀ i (T : HypergraphPiece Old), designatedOld T →
        attachedDesignatedSupport B S D f designatedOld
          (T.map (relationEmbeddingToFunction
            (RelStructure.Attachment.copyEmbedding B S D f i))) := by
    intro i T hT
    exact ⟨i, T, hT, rfl⟩
  exact ForestCompletionProperty.assemble_true_active_quantified
    A B S D f
    hSourceNonempty hSourceCover
    outer hOuterCore full hFull
    hActiveEdges hAmbientEdges m hLocalForest hALinear
    testedOld designatedOld hOld hTestActiveEdge
    (attachedTestedABSupport A B S D f designatedOld)
    (attachedDesignatedSupport B S D f designatedOld)
    hChooseOwner hDesignatedGlobal

end StructuralRamsey.Girth

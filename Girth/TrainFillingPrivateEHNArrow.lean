import Girth.TrainFillingRamseyIndexedChoices
import Girth.TrainFillingPrivateSelectedIndexedArrow

set_option Elab.async false

/-!
# The actual EHN arrow for a disjoint union of unequal first wagons

The existing EHN witness constructs a single coloured ordered X and a
closed-target Ramsey family for B = W. The old private-choice adapter
asked every first wagon F_p to be equivalent to W; this is generally
false, and has been removed here.

For each closed-target W-embedding b, compose it with the genuine
inclusion F_p -> W. The pair-closure certificate from EHN makes b
A-strong and transitivity makes each composite A-strong.
The first-wagon local target cover is supplied by its original edges.

This theorem constructs the WHOLE heterogeneous indexed private
family and derives the EXACT selectedCommonEdges local-arrow
hypothesis used in TrainFillingIndexedSelectedColourWord.
It uses no unconstructed separate monochromatic s_p and no output
M-copy/girth assumptions. The original EHN theorem remains the
explicit external Ramsey input.

A concrete relational model of the disjoint union W and its strong
component inclusions is still required at the cutoff-two call site;
the selected M-copy and global parentwise realization are separate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Girth.IndexedPrivateChoice

universe u v w

/-- The EHN closed-target Ramsey arrow, first applied to embeddings
of A into W, gives the same colour on the genuine physical support
edges of the single selected W-copy. The nonempty A-copy picks the
common colour without asking for a default arbitrary colour. -/
theorem closedTargetRamseyFamily_supportArrow
    {L : RelLanguage.{u}}
    {UA W X : Type v} {κ : Type w}
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (C : StructuralRamsey.Structure (closureLanguage L) X)
    (hRamsey : ClosedTargetRamseyFamily A B C κ)
    (hAB : Nonempty (RelStructure.Embedding A B))
    (ρ : {e : Set X // e ∈ supportCopies A (closureRelReduct C)} → κ) :
    ∃ (b : StructuralRamsey.Structure.Embedding
         (targetClosureExpansion A B) C)
      (colour : κ),
      ∀ a : RelStructure.Embedding A B,
        ρ ⟨copyCarrier ((targetEmbeddingRel b).comp a),
          ⟨(targetEmbeddingRel b).comp a, rfl⟩⟩ = colour := by
  classical
  let χ : RelStructure.Embedding A (closureRelReduct C) → κ :=
    fun a => ρ ⟨copyCarrier a, ⟨a, rfl⟩⟩
  obtain ⟨b, hb⟩ := hRamsey χ
  let a₀ : RelStructure.Embedding A B := Classical.choice hAB
  refine ⟨b, χ ((targetEmbeddingRel b).comp a₀), ?_⟩
  intro a
  change χ ((targetEmbeddingRel b).comp a) =
    χ ((targetEmbeddingRel b).comp a₀)
  exact hb a a₀

/-- The real closed-target EHN result produces every chosen summand
private extension and the common local-arrow for all first wagons,
even when the first wagons have different cardinalities. The
index CChoice consists of the genuinely selected closed embeddings,
not an arbitrary invented set of W-images. -/
theorem exists_colouredRamsey_unequalSummandPrivateChoices
    {L : RelLanguage.{u}}
    {UA W V P : Type v} {κ : Type w}
    (A : RelStructure L UA)
    (B : RelStructure L W)
    [LinearOrder UA] [LinearOrder W]
    [Finite UA] [Finite W]
    (hAirr : A.Irreducible)
    (hBlin : ALinear A B)
    (hmono : ∀ a : RelStructure.Embedding A B, StrictMono a)
    (hAB : Nonempty (RelStructure.Embedding A B))
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (include : (p : P) → RelStructure.Embedding (local p) B)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : RelStructure.Embedding A (local p), x ∈ copyCarrier a)
    [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X)
      (C : StructuralRamsey.Structure (closureLanguage L) X),
      ElementaryCAClass A C ∧
      ClosedTargetRamseyFamily A B C κ ∧
      ∃ (U :
        (StructuralRamsey.Structure.Embedding
          (targetClosureExpansion A B) C) →
          PrivateWagonInput V P X),
        ∃ (hTemplate : ∀ b, (U b).templateEdges =
          supportCopies A (closureRelReduct C)),
        ∀ ρ :
          {e : Set X // e ∈ supportCopies A (closureRelReduct C)} → κ,
          ∃ (b : StructuralRamsey.Structure.Embedding
               (targetClosureExpansion A B) C)
            (colour : κ),
            ∀ p : P,
              ∀ e : {e : Set X //
                e ∈ supportCopies A (closureRelReduct C)},
                e ∈ selectedCommonEdges U
                  (supportCopies A (closureRelReduct C))
                  hTemplate b p → ρ e = colour := by
  classical
  obtain ⟨X, hFinite, ord, C, hClass, hRamsey⟩ :=
    closedTargetRamseyFamily_of_monotone_embeddings
      A B hAirr hBlin hmono κ
  let Choice :=
    StructuralRamsey.Structure.Embedding
      (targetClosureExpansion A B) C
  let chosen : Choice → RelStructure.Embedding B (closureRelReduct C) :=
    fun b => targetEmbeddingRel b
  have hStrong : ∀ b : Choice,
      AStrong A (closureRelReduct C) (copyCarrier (chosen b)) := by
    intro b
    exact targetEmbedding_range_aStrong hClass.2 b
  let U : Choice → PrivateWagonInput V P X :=
    SummandPrivateTemplate.selectedUnionPrivateChoices
      A B (closureRelReduct C) oldCarrier local include
        hInclude hCovered chosen hStrong
  have hTemplate : ∀ b : Choice,
      (U b).templateEdges = supportCopies A (closureRelReduct C) := by
    intro b
    rfl
  refine ⟨X, hFinite, ord, C, hClass, hRamsey, U, hTemplate, ?_⟩
  have hFirstArrow :
      ∀ ρ : {e : Set X // e ∈ supportCopies A (closureRelReduct C)} → κ,
        ∃ (b : Choice) (colour : κ),
          ∀ a : RelStructure.Embedding A B,
            ρ ⟨copyCarrier ((chosen b).comp a),
                ⟨(chosen b).comp a, rfl⟩⟩ = colour := by
    intro ρ
    exact closedTargetRamseyFamily_supportArrow A B C
      hRamsey hAB ρ
  exact SummandPrivateTemplate.selectedUnionPrivateChoices_commonLocalArrow
    A B (closureRelReduct C) oldCarrier local include
      hInclude hCovered chosen hStrong hFirstArrow

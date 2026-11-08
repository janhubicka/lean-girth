import Girth.TrainFillingRamseyIndexedChoices
import Girth.TrainFillingIndexedEdgeFlatten

set_option Elab.async false

/-!
# The actual EHN closed-target Ramsey family chooses monochromatic W* edges

The cutoff-two proof colours every complete A-support edge of X by
the common word rho chosen by the shorter M→N Ramsey arrow.
A support edge is its physical vertex CARRIER, not an arbitrary
copy-embedding label.

To use the existing functional EHN closed-target Ramsey theorem,
colour each relational embedding a : A ↪ X by the colour rho of
its complete image support edge. EHN then chooses a full closed
B-copy b : B ↪ X for which this colour is constant on ALL
composites b ∘ a with a : A ↪ B.

The checked strong private-template construction has selected edges
EXACTLY the image carriers of those composites. Consequently every
actually selected local W* edge has the common colour. This is not
an independently assumed local monochromatic subfamily.

The proof is independent of the old-N selected M-copy, which is
chosen by the OTHER, shorter-train Ramsey arrow. Combining the
two choices with the physical colour-word transport is a separate
but now elementary endpoint. No appendix or stronger girth premise.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA W X : Type v} {κ : Type w}

/-- Monochromaticity on actual image A-embeddings in a strong B-copy
is exactly monochromaticity of ALL selected W* support edge carriers.
The proof does not require unique embedding labels for equal carriers. -/
theorem ofStrongEmbedding_selectedEdges_monochromatic
    (A : RelStructure L UA) (B : RelStructure L W)
    (R : RelStructure L X)
    (b : Embedding B R)
    (hStrong : AStrong A R (copyCarrier b))
    (hCovered : ∀ x : W, ∃ a : Embedding A B, x ∈ copyCarrier a)
    (ρ : {E : Set X // E ∈ supportCopies A R} → κ)
    (colour : κ)
    (hMono : ∀ a : Embedding A B,
      ρ ⟨copyCarrier (b.comp a), ⟨b.comp a, rfl⟩⟩ = colour)
    (e : {E : Set X // E ∈ supportCopies A R})
    (he : e ∈
      (UniformPrivateTemplate.ofStrongEmbedding
        A B R b hStrong hCovered).selectedEdges) :
    ρ e = colour := by
  change ∃ s : {F : Set W // F ∈ supportCopies A B},
    e.1 = b.toFunctionEmbedding '' s.1 at he
  obtain ⟨s, hs⟩ := he
  obtain ⟨a, ha⟩ := s.2
  have heq : e.1 = copyCarrier (b.comp a) := by
    calc
      e.1 = b.toFunctionEmbedding '' s.1 := hs
      _ = b.toFunctionEmbedding '' copyCarrier a :=
        congrArg (fun E : Set W => b.toFunctionEmbedding '' E) ha
      _ = copyCarrier (b.comp a) :=
        UniformPrivateTemplate.image_copyCarrier_comp A B R b a
  have hSubtype :
      e = (⟨copyCarrier (b.comp a),
            ⟨b.comp a, rfl⟩⟩ :
        {E : Set X // E ∈ supportCopies A R}) :=
    Subtype.ext heq
  rw [hSubtype]
  exact hMono a

/-- The VERIFIED closed-target EHN Ramsey arrow itself supplies one
genuinely selected strong B-copy W* in X whose ENTIRE local A-support
edge family is monochromatic for an arbitrary colour word on complete
physical A-support carriers.

The only nonemptiness required to choose a colour witness is that
B is nonempty and its vertices are covered by A-copies. This is
already the input of the EHN private-choice construction. -/
theorem closedTargetRamseyFamily_selectedEdges_monochromatic
    (A : RelStructure L UA) (B : RelStructure L W)
    [Nonempty W]
    (K : StructuralRamsey.Structure (closureLanguage L) X)
    (hRamsey : ClosedTargetRamseyFamily A B K κ)
    (hStrong : ∀ b : StructuralRamsey.Structure.Embedding
        (targetClosureExpansion A B) K,
      AStrong A (closureRelReduct K)
        (copyCarrier (targetEmbeddingRel b)))
    (hCovered : ∀ x : W, ∃ a : Embedding A B, x ∈ copyCarrier a)
    (ρ : {E : Set X // E ∈ supportCopies A (closureRelReduct K)} → κ) :
    ∃ (b : StructuralRamsey.Structure.Embedding
        (targetClosureExpansion A B) K)
      (colour : κ),
      ∀ e : {E : Set X // E ∈ supportCopies A (closureRelReduct K)},
        e ∈ (UniformPrivateTemplate.ofStrongEmbedding A B
          (closureRelReduct K) (targetEmbeddingRel b)
          (hStrong b) hCovered).selectedEdges →
        ρ e = colour := by
  let χ : Embedding A (closureRelReduct K) → κ :=
    fun a => ρ ⟨copyCarrier a, ⟨a, rfl⟩⟩
  obtain ⟨b, hb⟩ := hRamsey χ
  obtain ⟨x⟩ := (inferInstance : Nonempty W)
  obtain ⟨a₀, _⟩ := hCovered x
  refine ⟨b, χ ((targetEmbeddingRel b).comp a₀), ?_⟩
  intro e he
  exact ofStrongEmbedding_selectedEdges_monochromatic
    A B (closureRelReduct K) (targetEmbeddingRel b)
    (hStrong b) hCovered ρ
    (χ ((targetEmbeddingRel b).comp a₀))
    (fun a => hb a a₀) e he


/-- The actual EHN *heterogeneous* indexed private-choice family.
It is constructed from EVERY strong selected closed B-copy in X;
one choice c may have a different selected W* template edge
subfamily from another. No selected local family is invented. -/
noncomputable def ehnIndexedPrivateChoiceFamily
    {V P : Type v}
    (A : RelStructure L UA) (B : RelStructure L W)
    (K : StructuralRamsey.Structure (closureLanguage L) X)
    (hStrong : ∀ b : StructuralRamsey.Structure.Embedding
        (targetClosureExpansion A B) K,
      AStrong A (closureRelReduct K)
        (copyCarrier (targetEmbeddingRel b)))
    (hCovered : ∀ x : W, ∃ a : Embedding A B, x ∈ copyCarrier a)
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ W) :
    (StructuralRamsey.Structure.Embedding
      (targetClosureExpansion A B) K) → PrivateWagonInput V P X :=
  relationalPrivateChoices A B (closureRelReduct K)
    (fun b => targetEmbeddingRel b) hStrong hCovered
    oldCarrier identify

/-- Every EHN-indexed private choice uses exactly the SAME complete
ambient X support edge family. Only its selected W* subfamily varies. -/
@[simp] theorem ehnIndexedPrivateChoiceFamily_templateEdges
    {V P : Type v}
    (A : RelStructure L UA) (B : RelStructure L W)
    (K : StructuralRamsey.Structure (closureLanguage L) X)
    (hStrong : ∀ b : StructuralRamsey.Structure.Embedding
        (targetClosureExpansion A B) K,
      AStrong A (closureRelReduct K)
        (copyCarrier (targetEmbeddingRel b)))
    (hCovered : ∀ x : W, ∃ a : Embedding A B, x ∈ copyCarrier a)
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ W)
    (b : StructuralRamsey.Structure.Embedding
      (targetClosureExpansion A B) K) :
    (ehnIndexedPrivateChoiceFamily A B K hStrong hCovered
      oldCarrier identify b).templateEdges =
      supportCopies A (closureRelReduct K) := rfl

/-- The actual EHN closed-target Ramsey family, after the REAL
heterogeneous indexed private construction, satisfies the exact
local monochromaticity interface needed by the final colour-word
argument: one selected choice c and one colour work at ALL its
first-wagon labels p, without any per-wagon colour choice.

The local edge e is a physical common support carrier in X.
The result follows from the EHN composite A-copy arrow and the
literal selectedEdges definition of the private template; it is
not an independently assumed hLocalArrow field. -/
theorem closedTargetRamseyFamily_indexedSelectedEdges_monochromatic
    {V P : Type v}
    (A : RelStructure L UA) (B : RelStructure L W)
    [Nonempty W]
    (K : StructuralRamsey.Structure (closureLanguage L) X)
    (hRamsey : ClosedTargetRamseyFamily A B K κ)
    (hStrong : ∀ b : StructuralRamsey.Structure.Embedding
        (targetClosureExpansion A B) K,
      AStrong A (closureRelReduct K)
        (copyCarrier (targetEmbeddingRel b)))
    (hCovered : ∀ x : W, ∃ a : Embedding A B, x ∈ copyCarrier a)
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ W)
    (ρ : {E : Set X // E ∈ supportCopies A (closureRelReduct K)} → κ) :
    ∃ (b : StructuralRamsey.Structure.Embedding
          (targetClosureExpansion A B) K)
        (colour : κ),
      ∀ p : P,
      ∀ e : {E : Set X // E ∈ supportCopies A (closureRelReduct K)},
        e ∈ IndexedPrivateChoice.selectedCommonEdges
          (ehnIndexedPrivateChoiceFamily A B K hStrong
            hCovered oldCarrier identify)
          (supportCopies A (closureRelReduct K))
          (fun c => ehnIndexedPrivateChoiceFamily_templateEdges
            A B K hStrong hCovered oldCarrier identify c)
          b p →
        ρ e = colour := by
  let U := ehnIndexedPrivateChoiceFamily A B K hStrong
    hCovered oldCarrier identify
  let hTemplate : ∀ c, (U c).templateEdges =
      supportCopies A (closureRelReduct K) := by
    intro c
    exact ehnIndexedPrivateChoiceFamily_templateEdges
      A B K hStrong hCovered oldCarrier identify c
  obtain ⟨b, colour, hLocal⟩ :=
    closedTargetRamseyFamily_selectedEdges_monochromatic
      A B K hRamsey hStrong hCovered ρ
  refine ⟨b, colour, ?_⟩
  intro p e he
  change e ∈ IndexedPrivateChoice.selectedCommonEdges U
    (supportCopies A (closureRelReduct K)) hTemplate b p at he
  obtain ⟨e₀, he₀, heq⟩ := he
  have hSelected :
      e₀ ∈ (UniformPrivateTemplate.ofStrongEmbedding
        A B (closureRelReduct K) (targetEmbeddingRel b)
        (hStrong b) hCovered).selectedEdges := by
    change e₀ ∈
      (relationalPrivateChoices A B (closureRelReduct K)
        (fun c => targetEmbeddingRel c) hStrong hCovered
        oldCarrier identify b).selectedEdges p at he₀
    rw [relationalPrivateChoices_selectedEdges
      A B (closureRelReduct K) (fun c => targetEmbeddingRel c)
      hStrong hCovered oldCarrier identify b p] at he₀
    exact he₀
  have hValue : e₀.1 = e.1 := by
    exact congrArg Subtype.val heq
  have hSubtype :
      (e₀ : {E : Set X // E ∈ supportCopies A (closureRelReduct K)}) = e :=
    Subtype.ext hValue
  have hColour := hLocal e₀ hSelected
  rw [hSubtype] at hColour
  exact hColour


end StructuralRamsey.Girth

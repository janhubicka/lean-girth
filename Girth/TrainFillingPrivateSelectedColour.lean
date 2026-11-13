import Girth.TrainFillingPrivateSelectedUnion

set_option Elab.async false

/-!
# Monochromatic first-wagon summands of one selected W-copy

The EHN arrow chooses one selected copy s : W -> X of the ordered
DISJOINT UNION W of all original first wagons F_p. Its monochromatic
A-support edges necessarily include the s(u_p(a)) edges for every
A-copy a in every F_p, with the SAME colour.

This is an exact algebraic input to the second, indexed colour-word
arrow; it needs no isomorphisms F_p ≃ W and does not choose an unrelated
local W-copy separately for each first-wagon label p.

The elementary first theorem works with any two composable relational
embeddings. The second theorem specializes it to the actual
unequal-summand private input from TrainFillingPrivateSelectedUnion.
It remains conditional on the first EHN arrow providing s and its
monochromatic W-image; constructing the complete lower-stage selected
M-copy and target family is a different task.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w

/-- A monochromatic selected copy of W makes every support edge of
the image of a smaller F -> W monochromatic, with the SAME colour.
The image is an actual A-support edge of R, not an untyped carrier. -/
theorem selectedUnion_summand_monochromatic
    {L : RelLanguage.{u}}
    {UA F W X : Type v} {κ : Type w}
    (A : RelStructure L UA)
    (Fstruct : RelStructure L F)
    (Wstruct : RelStructure L W)
    (R : RelStructure L X)
    (inc : RelStructure.Embedding Fstruct Wstruct)
    (selected : RelStructure.Embedding Wstruct R)
    (ρ : {a : Set X // a ∈ supportCopies A R} → κ)
    (colour : κ)
    (hW : ∀ a : RelStructure.Embedding A Wstruct,
      ρ ⟨copyCarrier (selected.comp a),
        ⟨selected.comp a, rfl⟩⟩ = colour)
    (e : {a : Set X // a ∈ supportCopies A R})
    (hEdge : ∃ a : RelStructure.Embedding A Fstruct,
      e.1 = copyCarrier (selected.comp (inc.comp a))) :
    ρ e = colour := by
  rcases hEdge with ⟨a, ha⟩
  have heq : e =
      (⟨copyCarrier (selected.comp (inc.comp a)),
        ⟨selected.comp (inc.comp a), rfl⟩⟩ :
        {a : Set X // a ∈ supportCopies A R}) :=
    Subtype.ext ha
  rw [heq]
  exact hW (inc.comp a)

namespace SummandPrivateTemplate

/-- In the constructed unequal-summand family, one EHN
monochromatic W-embedding gives one common colour on the ENTIRE
selected local X-edge family in EVERY first wagon p. This is the
precise local-arrow input for the existing indexed colour-word
transfer, and avoids requiring F_p ≃ W. -/
theorem selectedEdges_monochromatic_of_selectedUnion
    {L : RelLanguage.{u}}
    {UA W X V P : Type v} {κ : Type w}
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (R : RelStructure L X)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (include : (p : P) → RelStructure.Embedding (local p) B)
    (selected : RelStructure.Embedding B R)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hSelected : AStrong A R (copyCarrier selected))
    (hCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : RelStructure.Embedding A (local p), x ∈ copyCarrier a)
    (ρ : {a : Set X // a ∈ supportCopies A R} → κ)
    (colour : κ)
    (hW : ∀ a : RelStructure.Embedding A B,
      ρ ⟨copyCarrier (selected.comp a),
        ⟨selected.comp a, rfl⟩⟩ = colour)
    (p : P) (e : {a : Set X // a ∈ supportCopies A R})
    (he : e ∈
      (fromSelectedUnion A B R oldCarrier local include selected
        hInclude hSelected hCovered).selectedEdges p) :
    ρ e = colour := by
  obtain ⟨f, hf⟩ := he
  change f.1 ∈ supportCopies A (local p) at f.2
  obtain ⟨a, ha⟩ := f.2
  have hfImage :
      e.1 = (selected.comp (include p)).toFunctionEmbedding '' f.1 := by
    exact hf
  have hComp :
      (selected.comp (include p)).comp a =
        selected.comp ((include p).comp a) := by
    apply RelStructure.Embedding.ext
    intro x
    rfl
  have hEdge :
      e.1 = copyCarrier (selected.comp ((include p).comp a)) := by
    calc
      e.1 = (selected.comp (include p)).toFunctionEmbedding '' f.1 := hfImage
      _ = (selected.comp (include p)).toFunctionEmbedding '' copyCarrier a :=
        congrArg _ ha
      _ = copyCarrier ((selected.comp (include p)).comp a) :=
        UniformPrivateTemplate.image_copyCarrier_comp
          A (local p) R (selected.comp (include p)) a
      _ = copyCarrier (selected.comp ((include p).comp a)) :=
        congrArg copyCarrier hComp
  exact selectedUnion_summand_monochromatic A (local p) B R
    (include p) selected ρ colour hW e
      ⟨a, hEdge⟩

end SummandPrivateTemplate
end StructuralRamsey.Girth

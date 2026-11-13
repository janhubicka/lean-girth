import Girth.TrainFillingPrivateSelectedColour

set_option Elab.async false

/-!
# One Ramsey family of unequal first-wagon private extensions

The first Ramsey theorem is applied to W, the disjoint union of
the original first wagons, not separately to each F_p.

For a genuine selected embedding s_c : W -> X, produce the entire
heterogeneous private input U_c at once. All choices share exactly
the same ambient template-edge set E(X), while the selected edges
inside individual first wagons can differ with c and p.

The final theorem converts the ordinary monochromatic W-copy
arrow into the local-arrow interface needed for indexed filling.
No selected copy of the contracted M, nor its ambient parentwise
realization, is fabricated here.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w

namespace SummandPrivateTemplate

/-- Genuine indexed family built from selected embeddings of the
single ordered disjoint union W. The different first-wagon types
are not required to be isomorphic to W or to one another. -/
noncomputable def selectedUnionPrivateChoices
    {L : RelLanguage.{u}}
    {UA W X V P C : Type v}
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (R : RelStructure L X)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (include : (p : P) → RelStructure.Embedding (local p) B)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : RelStructure.Embedding A (local p), x ∈ copyCarrier a)
    (choice : C → RelStructure.Embedding B R)
    (hStrong : ∀ c, AStrong A R (copyCarrier (choice c))) :
    C → PrivateWagonInput V P X :=
  fun c =>
    (fromSelectedUnion A B R oldCarrier local include
      (choice c) hInclude (hStrong c) hCovered).toPrivateWagonInput

/-- The complete ambient template family does not depend on which
W-copy or original first wagon was chosen. -/
theorem selectedUnionPrivateChoices_templateEdges
    {L : RelLanguage.{u}}
    {UA W X V P C : Type v}
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (R : RelStructure L X)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (include : (p : P) → RelStructure.Embedding (local p) B)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : RelStructure.Embedding A (local p), x ∈ copyCarrier a)
    (choice : C → RelStructure.Embedding B R)
    (hStrong : ∀ c, AStrong A R (copyCarrier (choice c)))
    (c : C) :
    (selectedUnionPrivateChoices A B R oldCarrier local include
      hInclude hCovered choice hStrong c).templateEdges =
      supportCopies A R := rfl

/-- Monochromaticity of one *entire* selected W-copy under each
word-colouring yields a single colour for all selected local edges
of every first wagon in that same choice. No independent
monochromatic choices for different p are required. -/
theorem selectedUnionPrivateChoices_localArrow
    {L : RelLanguage.{u}}
    {UA W X V P C : Type v} {κ : Type w}
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (R : RelStructure L X)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (include : (p : P) → RelStructure.Embedding (local p) B)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : RelStructure.Embedding A (local p), x ∈ copyCarrier a)
    (choice : C → RelStructure.Embedding B R)
    (hStrong : ∀ c, AStrong A R (copyCarrier (choice c)))
    (hArrow : ∀ ρ : {a : Set X // a ∈ supportCopies A R} → κ,
      ∃ (c : C) (colour : κ),
        ∀ a : RelStructure.Embedding A B,
          ρ ⟨copyCarrier ((choice c).comp a),
              ⟨(choice c).comp a, rfl⟩⟩ = colour)
    (ρ : {a : Set X // a ∈ supportCopies A R} → κ) :
    ∃ (c : C) (colour : κ),
      ∀ (p : P) (e : {a : Set X // a ∈ supportCopies A R}),
        e ∈ (selectedUnionPrivateChoices A B R oldCarrier
            local include hInclude hCovered choice hStrong c).selectedEdges p →
          ρ e = colour := by
  obtain ⟨c, colour, hMono⟩ := hArrow ρ
  refine ⟨c, colour, ?_⟩
  intro p e he
  exact selectedEdges_monochromatic_of_selectedUnion
    A B R oldCarrier local include (choice c)
      hInclude (hStrong c) hCovered ρ colour
      hMono p e he

end SummandPrivateTemplate
end StructuralRamsey.Girth

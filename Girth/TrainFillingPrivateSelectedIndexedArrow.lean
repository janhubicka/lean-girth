import Girth.TrainFillingPrivateSelectedFamily
import Girth.TrainFillingIndexedEdgeFlatten

set_option Elab.async false

/-!
# Exact selected-common-edge arrow for unequal first-wagon summands

The indexed filling colour-word theorem expects a local arrow phrased
using the fixed CommonTemplateEdge type and selectedCommonEdges
transported through choiceTemplateEquiv. The first EHN arrow instead
speaks about actual A-embeddings into the disjoint union W.

The checked-looking algebraic adapter below transports the result
from one selected W-copy to exactly the selectedCommonEdges required
by the indexed physical filling. No independent p-wise choice,
no copy of W in every F_p, and no restriction of ambient edges.

This is a proof candidate until exact-head Lean and axiom checks.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Girth.IndexedPrivateChoice

universe u v w

namespace SummandPrivateTemplate

/-- Global monochromaticity of one W-copy yields the exact
selectedCommonEdges local arrow interface of the heterogeneous
indexed filling. The same selected c and colour work for every p. -/
theorem selectedUnionPrivateChoices_commonLocalArrow
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
              ⟨(choice c).comp a, rfl⟩⟩ = colour) :
    let U := selectedUnionPrivateChoices A B R oldCarrier local
      include hInclude hCovered choice hStrong
    ∀ ρ : {a : Set X // a ∈ supportCopies A R} → κ,
      ∃ (c : C) (colour : κ),
        ∀ (p : P) (e : {a : Set X // a ∈ supportCopies A R}),
          e ∈ selectedCommonEdges U (supportCopies A R)
            (fun c => selectedUnionPrivateChoices_templateEdges
              A B R oldCarrier local include hInclude hCovered
              choice hStrong c) c p →
            ρ e = colour := by
  let U := selectedUnionPrivateChoices A B R oldCarrier local
    include hInclude hCovered choice hStrong
  let hTemplate : ∀ c : C, (U c).templateEdges = supportCopies A R :=
    fun c => selectedUnionPrivateChoices_templateEdges
      A B R oldCarrier local include hInclude hCovered
        choice hStrong c
  intro ρ
  obtain ⟨c, colour, hLocal⟩ :=
    selectedUnionPrivateChoices_localArrow A B R oldCarrier local
      include hInclude hCovered choice hStrong hArrow ρ
  refine ⟨c, colour, ?_⟩
  intro p e he
  change e ∈ selectedCommonEdges U (supportCopies A R) hTemplate c p at he
  obtain ⟨f, hf, hfe⟩ := he
  have hEq : (choiceTemplateEquiv U (supportCopies A R) hTemplate c f) =
      (f : {a : Set X // a ∈ supportCopies A R}) := by
    apply Subtype.ext
    rfl
  have hMem :
      (choiceTemplateEquiv U (supportCopies A R) hTemplate c f) ∈
        (U c).selectedEdges p := by
    rw [hEq]
    exact hf
  have hColour :=
    hLocal p (choiceTemplateEquiv U (supportCopies A R) hTemplate c f) hMem
  rwa [← hfe] at hColour

end SummandPrivateTemplate
end StructuralRamsey.Girth

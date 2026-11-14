import Girth.TrainFillingPrivateMonotoneSummands

set_option Elab.async false

/-!
# Derive the contracted M colour compatibility from the chosen union

The checked actual coloured M-support theorem expects hColour:
  oldColour(v) = templateColour(coordinate(c,p,v)).
This is not a new combinatorial property of the filling. It
is forced by the two actual relational unary-colour embeddings:

* the old first wagon F_p embeds into the tagged disjoint union W
  with its original vertex colours;
* the EHN-selected copy W -> X preserves those same unary colours.

Their composition is exactly the coordinate(c,p) used by the
private-extension construction. Hence hColour is a consequence,
not an independent premise, once the genuine coloured structures
and their actual embeddings have been supplied.

No assumption that all possible EHN closed-target embeddings
preserve the auxiliary total order is used. We apply this to
the separately restricted MONOTONE choice family.

Candidate source, pending exact-head Lean compilation.
-/

namespace StructuralRamsey.Girth.SummandPrivateTemplate

open StructuralRamsey.RelStructure

universe u v w

/-- The component and selected-union colour equalities imply the
exact old-to-X coordinate colour condition needed by the actual
heterogeneous coloured contracted M theorem, for EVERY choice
and EVERY first wagon at once. -/
theorem selectedUnionPrivateChoices_colourCompatibility
    {L : RelLanguage.{u}}
    {UA W X V P C : Type v} {I : Type w}
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (R : RelStructure L X)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (include : (p : P) → Embedding (local p) B)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : Embedding A (local p), x ∈ copyCarrier a)
    (choice : C → Embedding B R)
    (hStrong : ∀ c, AStrong A R (copyCarrier (choice c)))
    (oldColour : V → I)
    (unionColour : W → I)
    (templateColour : X → I)
    (hOld : ∀ p (z : {x : V // x ∈ oldCarrier p}),
      oldColour z.1 = unionColour (include p z))
    (hSelected : ∀ c (w : W),
      unionColour w = templateColour (choice c w)) :
    let U := selectedUnionPrivateChoices A B R
      oldCarrier local include hInclude hCovered choice hStrong
    ∀ c p (z : {x : V // x ∈ (U c).oldCarrier p}),
      oldColour z.1 = templateColour ((U c).coordinate p z) := by
  intro c p z
  change oldColour z.1 = templateColour (choice c (include p z))
  exact (hOld p z).trans (hSelected c (include p z))

/-- The SAME equality specialized to the genuine monotone
closed-target EHN choices, not to arbitrary unlabelled W-images.
No coordinate-colour compatibility has to be postulated after
the original two component/selected relational embeddings. -/
theorem monotoneSelectedUnion_colourCompatibility
    {L : RelLanguage.{u}}
    {UA W X V P : Type v} {I : Type w}
    [LinearOrder W] [LinearOrder X]
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (R : StructuralRamsey.Structure (closureLanguage L) X)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (include : (p : P) → Embedding (local p) B)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : Embedding A (local p), x ∈ copyCarrier a)
    (hClass : ElementaryCAClass A R)
    (oldColour : V → I) (unionColour : W → I)
    (templateColour : X → I)
    (hOld : ∀ p (z : {x : V // x ∈ oldCarrier p}),
      oldColour z.1 = unionColour (include p z))
    (hSelected : ∀ (c : MonotoneClosedChoice A B R) (w : W),
      unionColour w = templateColour ((targetEmbeddingRel c.1) w)) :
    let U := monotoneSelectedUnionPrivateChoices A B R
      oldCarrier local include hInclude hCovered hClass
    ∀ c p (z : {x : V // x ∈ (U c).oldCarrier p}),
      oldColour z.1 = templateColour ((U c).coordinate p z) := by
  exact selectedUnionPrivateChoices_colourCompatibility
    A B (closureRelReduct R)
      oldCarrier local include hInclude hCovered
      (fun c : MonotoneClosedChoice A B R => targetEmbeddingRel c.1)
      (fun c => targetEmbedding_range_aStrong hClass.2 c.1)
      oldColour unionColour templateColour hOld hSelected

end StructuralRamsey.Girth.SummandPrivateTemplate

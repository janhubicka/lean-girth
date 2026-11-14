import Girth.TrainFillingPrivateMonotoneEHN
import Girth.TrainFillingPrivateSelectedIndexedArrow

set_option Elab.async false

/-!
# Use only genuinely order-preserving EHN choices

ClosedTargetRamseyFamily on its own forgets the ordered selection
of W in X. The direct cutoff-two construction needs the selected
coordinate maps s_p = s ∘ u_p to be increasing so that each
contracted first wagon has the prescribed colour-block order.

Here the EHN choice type is the subtype of genuine closed
target embeddings with an explicit StrictMono certificate. The
stronger ordered EHN arrow supplies a monochromatic witness
INSIDE this restricted type, not just among all closed embeddings.

All private summands still come from the SAME selected s and
share exactly the same X support-edge family. The proof also
shows each local coordinate is increasing when the original
component inclusions u_p are increasing.

This is candidate source pending Lean compilation. The global
block order on X (which must extend the within-predicate orders
and place colours in their prescribed sequence) is a separate
actual ordered-presentation construction at the cutoff-two site.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Girth.IndexedPrivateChoice

universe u v w

namespace SummandPrivateTemplate

/-- Selected closed EHN embeddings with their retained increasing
auxiliary-order certificate. The subtype excludes nonmonotone
closure embeddings rather than falsely asserting all are monotone. -/
abbrev MonotoneClosedChoice
    {L : RelLanguage.{u}}
    {UA W X : Type v} [LinearOrder W] [LinearOrder X]
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (R : StructuralRamsey.Structure (closureLanguage L) X) :=
  {b : StructuralRamsey.Structure.Embedding
       (targetClosureExpansion A B) R //
     StrictMono (targetEmbeddingRel b)}

/-- The complete heterogeneous private-choice family indexed ONLY
by certified monotone closed-target embeddings. The C type is an
actual subtype of selected EHN embeddings, not a new arbitrary
set of formal copies. -/
noncomputable def monotoneSelectedUnionPrivateChoices
    {L : RelLanguage.{u}}
    {UA W X V P : Type v}
    [LinearOrder W] [LinearOrder X]
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (R : StructuralRamsey.Structure (closureLanguage L) X)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (include : (p : P) → RelStructure.Embedding (local p) B)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : RelStructure.Embedding A (local p), x ∈ copyCarrier a)
    (hClass : ElementaryCAClass A R) :
    MonotoneClosedChoice A B R → PrivateWagonInput V P X :=
  selectedUnionPrivateChoices A B (closureRelReduct R)
    oldCarrier local include hInclude hCovered
    (fun c => targetEmbeddingRel c.1)
    (fun c => targetEmbedding_range_aStrong hClass.2 c.1)

/-- Every old F_p-coordinate preserves the actual auxiliary order
because both its embedding into W and the EHN-selected W-embedding
into X preserve their respective orders. No monotonicity assumption
on the resulting coordinate is supplied. -/
theorem monotoneSelectedUnion_coordinate_strictMono
    {L : RelLanguage.{u}}
    {UA W X V P : Type v}
    [LinearOrder V] [LinearOrder W] [LinearOrder X]
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (R : StructuralRamsey.Structure (closureLanguage L) X)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (include : (p : P) → RelStructure.Embedding (local p) B)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hIncludeMono : ∀ p, StrictMono (include p))
    (hCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : RelStructure.Embedding A (local p), x ∈ copyCarrier a)
    (hClass : ElementaryCAClass A R)
    (c : MonotoneClosedChoice A B R) (p : P) :
    StrictMono
      ((monotoneSelectedUnionPrivateChoices A B R oldCarrier local
        include hInclude hCovered hClass c).coordinate p) := by
  change StrictMono (fun x : {x : V // x ∈ oldCarrier p} =>
    targetEmbeddingRel c.1 (include p x))
  exact c.2.comp (hIncludeMono p)

/-- The real EHN arrow, now restricted to monotone selected
W-copies, yields a common colour for ALL selected first-wagon
local template edges of ONE such W-copy. -/
theorem monotoneSelectedUnion_commonLocalArrow
    {L : RelLanguage.{u}}
    {UA W X V P : Type v} {κ : Type w}
    [LinearOrder W] [LinearOrder X]
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (R : StructuralRamsey.Structure (closureLanguage L) X)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (include : (p : P) → RelStructure.Embedding (local p) B)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : RelStructure.Embedding A (local p), x ∈ copyCarrier a)
    (hClass : ElementaryCAClass A R)
    (hMonotoneArrow : ∀ χ :
      RelStructure.Embedding A (closureRelReduct R) → κ,
      ∃ b : StructuralRamsey.Structure.Embedding
        (targetClosureExpansion A B) R,
        StrictMono (targetEmbeddingRel b) ∧
        ∀ a₁ a₂ : RelStructure.Embedding A B,
          χ ((targetEmbeddingRel b).comp a₁) =
            χ ((targetEmbeddingRel b).comp a₂))
    (hAB : Nonempty (RelStructure.Embedding A B))
    (ρ : {e : Set X // e ∈ supportCopies A (closureRelReduct R)} → κ) :
    let U := monotoneSelectedUnionPrivateChoices A B R
      oldCarrier local include hInclude hCovered hClass
    ∃ (c : MonotoneClosedChoice A B R) (colour : κ),
      ∀ p : P, ∀ e :
        {e : Set X // e ∈ supportCopies A (closureRelReduct R)},
        e ∈ selectedCommonEdges U (supportCopies A (closureRelReduct R))
          (fun c => selectedUnionPrivateChoices_templateEdges
            A B (closureRelReduct R) oldCarrier local include
              hInclude hCovered
              (fun c : MonotoneClosedChoice A B R =>
                targetEmbeddingRel c.1)
              (fun c => targetEmbedding_range_aStrong hClass.2 c.1)
              c) c p → ρ e = colour := by
  let U := monotoneSelectedUnionPrivateChoices A B R
    oldCarrier local include hInclude hCovered hClass
  let chosen : MonotoneClosedChoice A B R →
      RelStructure.Embedding B (closureRelReduct R) :=
    fun c => targetEmbeddingRel c.1
  have hStrong : ∀ c : MonotoneClosedChoice A B R,
      AStrong A (closureRelReduct R) (copyCarrier (chosen c)) :=
    fun c => targetEmbedding_range_aStrong hClass.2 c.1
  have hFirstArrow :
      ∀ words : {e : Set X // e ∈ supportCopies A (closureRelReduct R)} → κ,
        ∃ (c : MonotoneClosedChoice A B R) (colour : κ),
          ∀ a : RelStructure.Embedding A B,
            words ⟨copyCarrier ((chosen c).comp a),
                  ⟨(chosen c).comp a, rfl⟩⟩ = colour := by
    intro words
    let χ : RelStructure.Embedding A (closureRelReduct R) → κ :=
      fun a => words ⟨copyCarrier a, ⟨a, rfl⟩⟩
    obtain ⟨b, hbMono, hbWord⟩ := hMonotoneArrow χ
    let a₀ : RelStructure.Embedding A B := Classical.choice hAB
    refine ⟨⟨b, hbMono⟩, χ ((targetEmbeddingRel b).comp a₀), ?_⟩
    intro a
    change χ ((targetEmbeddingRel b).comp a) =
      χ ((targetEmbeddingRel b).comp a₀)
    exact hbWord a a₀
  exact selectedUnionPrivateChoices_commonLocalArrow
    A B (closureRelReduct R) oldCarrier local include
      hInclude hCovered chosen hStrong hFirstArrow ρ

end SummandPrivateTemplate
end StructuralRamsey.Girth

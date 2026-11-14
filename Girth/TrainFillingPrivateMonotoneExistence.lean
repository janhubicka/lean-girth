import Girth.TrainFillingPrivateMonotoneSummands

set_option Elab.async false

/-!
# Concrete EHN output for UNEQUAL first wagons with ordered choices

The usual EHN closed-target Ramsey family forgets the auxiliary
order of its actual selected embedding. The direct cutoff-two
construction MUST keep that order for the fully coloured M.

This result packages the stronger ordered EHN witness, restricts
choices to increasing closed W-embeddings, and constructs ALL
private first-wagon templates with a common full X-support family.
It proves that every local first-wagon coordinate is strictly
increasing in the retained auxiliary orders and that the
monochromatic EHN W-copy gives ONE selected choice c with all
selected local X-edges of every original first wagon monochromatic.

The first wagons may have different sizes and types. Each local
inclusion F_p -> W is a genuine strong and increasing embedding;
there is no F_p ≃ W or unrelated selected W-copy per p.

The actual colour BLOCK order on X, and the ordered relational
presentation of the contracted M, are separate applications of
TrainFillingPrivateColourBlockOrder and earlier checked coloured
choice insertion theorems. This existence statement is a candidate
until exact-head Lean compilation.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Girth.IndexedPrivateChoice

universe u v w

namespace SummandPrivateTemplate

/-- EHN genuinely produces all unequal first-wagon private
choices with one common X, monotone coordinates, and the full
selected-common-edge monochromaticity arrow.

The returned X-order is EHN's auxiliary ordered Ramsey output;
no unsupported global colour-block condition is bundled in. -/
theorem exists_colouredRamsey_monotoneUnequalSummands
    {L : RelLanguage.{u}}
    {UA W V P : Type v} {κ : Type w}
    [LinearOrder UA] [LinearOrder W] [LinearOrder V]
    [Finite UA] [Finite W]
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (hAirr : A.Irreducible)
    (hBlin : ALinear A B)
    (hmono : ∀ a : RelStructure.Embedding A B, StrictMono a)
    (hAB : Nonempty (RelStructure.Embedding A B))
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (include : (p : P) → RelStructure.Embedding (local p) B)
    (hInclude : ∀ p, AStrong A B (copyCarrier (include p)))
    (hIncludeMono : ∀ p, StrictMono (include p))
    (hCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : RelStructure.Embedding A (local p), x ∈ copyCarrier a)
    [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X)
      (R : StructuralRamsey.Structure (closureLanguage L) X),
      ElementaryCAClass A R ∧
      (letI : LinearOrder X := o
       ∃ (U : MonotoneClosedChoice A B R →
          PrivateWagonInput V P X),
         ∃ (hTemplate : ∀ c, (U c).templateEdges =
              supportCopies A (closureRelReduct R)),
           (∀ c p, StrictMono ((U c).coordinate p)) ∧
           ∀ ρ : {e : Set X //
                   e ∈ supportCopies A (closureRelReduct R)} → κ,
             ∃ (c : MonotoneClosedChoice A B R) (colour : κ),
               ∀ p : P, ∀ e : {e : Set X //
                   e ∈ supportCopies A (closureRelReduct R)},
                 e ∈ selectedCommonEdges U
                   (supportCopies A (closureRelReduct R))
                   hTemplate c p → ρ e = colour) := by
  classical
  obtain ⟨X, hFinite, o, R, hClass, hMonotoneArrow⟩ :=
    monotoneClosedTargetRamseyFamily_of_monotone_embeddings
      A B hAirr hBlin hmono κ
  letI : LinearOrder X := o
  let U : MonotoneClosedChoice A B R → PrivateWagonInput V P X :=
    monotoneSelectedUnionPrivateChoices A B R
      oldCarrier local include hInclude hCovered hClass
  have hTemplate :
      ∀ c : MonotoneClosedChoice A B R,
        (U c).templateEdges = supportCopies A (closureRelReduct R) := by
    intro c
    rfl
  refine ⟨X, hFinite, o, R, hClass, U, hTemplate, ?_, ?_⟩
  · intro c p
    exact monotoneSelectedUnion_coordinate_strictMono
      A B R oldCarrier local include hInclude hIncludeMono
        hCovered hClass c p
  · intro ρ
    exact monotoneSelectedUnion_commonLocalArrow
      A B R oldCarrier local include
        hInclude hCovered hClass hMonotoneArrow hAB ρ

end SummandPrivateTemplate
end StructuralRamsey.Girth

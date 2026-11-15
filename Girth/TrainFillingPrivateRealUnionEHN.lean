import Girth.TrainFillingPrivateRealUnionOrder
import Girth.TrainFillingPrivateRealUnionLinear
import Girth.TrainFillingPrivateMonotoneExistence

set_option Elab.async false

/-!
# Actual tagged unequal first-wagon input to the ordered EHN theorem

This file is the concrete bridge from the original first-wagon
relational structures to the EHN target used in the direct
cutoff-two argument. It derives, rather than assumes:

* B = disjointUnion_p F_p has EXACT labelled, induced copies F_p;
* B is A-linear from local A-linearity;
* all A-embeddings into B are increasing from the genuine local
  monotonicity and the colour-first order on B;
* every component F_p -> B is itself increasing and A-strong;
* B is covered when the original first wagons are covered;
* B contains an A-copy when at least one old first-wagon vertex exists.

The global existence corollary therefore instantiates the already
written ordered EHN private-summand theorem without synthetic
hBlin, hInclude, hIncludeMono, hIncludeStrong or hAB inputs.

The remaining application is to obtain the coloured/local
hypotheses from the original E_a train (and Track 1's actual
covered, marked Ramsey witness), then retype to the covered X.

Uncompiled source candidate: no new axiom, sorry or output girth
hypothesis. Exact-head Lean and #print axioms remain necessary.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Girth.IndexedPrivateChoice

universe u v w

variable {L : RelLanguage.{u}}
variable {UA V P : Type v} {I : Type u}
variable [LinearOrder UA] [LinearOrder V] [LinearOrder P]
variable [LinearOrder I] [Finite UA] [Finite V] [Finite P]

/-- A nonempty true first-wagon vertex and its actual
local A-coverage furnish a genuine A-copy of W. -/
theorem firstWagonDisjointUnion_hasACopy
    (A : RelStructure L UA)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (hLocalCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : Embedding A (local p), x ∈ copyCarrier a)
    (hNonempty : Nonempty (FirstWagonUnionVertex oldCarrier)) :
    Nonempty (Embedding A (firstWagonDisjointUnion oldCarrier local)) := by
  obtain ⟨⟨p, x⟩⟩ := hNonempty
  obtain ⟨a, _hx⟩ := hLocalCovered p x
  exact ⟨(firstWagonSummandEmbedding oldCarrier local hPositive p).comp a⟩

/-- The GENUINE tagged W has exactly the ordered EHN
preconditions, from the original local first-wagon data.
No assumption that every future EHN X-copy is increasing. -/
theorem realFirstWagonDisjointUnion_monotoneEHN
    {κ : Type w}
    (A : RelStructure L UA)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (hSpan : HasSpanningRelation A)
    (oldColour : V → I)
    (hOldBlocks : ∀ x y : V,
      oldColour x ≠ oldColour y →
      x < y → oldColour x < oldColour y)
    (hLocalLinear : ∀ p, ALinear A (local p))
    (hLocalMono : ∀ p, ∀ a : Embedding A (local p),
      StrictMono a)
    [Fintype κ] [Nonempty κ] :
    let B := firstWagonDisjointUnion oldCarrier local
    letI : LinearOrder (FirstWagonUnionVertex oldCarrier) :=
      firstWagonUnionOrder oldCarrier oldColour
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X)
      (R : StructuralRamsey.Structure (closureLanguage L) X),
      ElementaryCAClass A R ∧
      MonotoneClosedTargetRamseyFamily A B o R κ := by
  let B := firstWagonDisjointUnion oldCarrier local
  letI : LinearOrder (FirstWagonUnionVertex oldCarrier) :=
    firstWagonUnionOrder oldCarrier oldColour
  have hLinear : ALinear A B :=
    firstWagonDisjointUnion_aLinear A oldCarrier local
      hPositive hSpan hLocalLinear
  have hMonotone : ∀ a : Embedding A B, StrictMono a :=
    firstWagonDisjointUnion_allACopies_strictMono
      A oldCarrier local hPositive hSpan
      oldColour hOldBlocks hLocalMono
  exact monotoneClosedTargetRamseyFamily_of_monotone_embeddings
    A B (irreducible_of_spanningRelation A hSpan) hLinear hMonotone κ

/-- EHN supplies all actual DIFFERENT first-wagon private
extensions from one selected W-copy, with increasing
coordinate maps and one common selected-edge colour.

All synthetic uniform-wagon and unordered-selection hypotheses
have been removed. The remaining inputs belong only to
the genuine original F_p structures and their vertex orders. -/
theorem realFirstWagonDisjointUnion_privateEHN
    {κ : Type w}
    (A : RelStructure L UA)
    (oldCarrier : P → Set V)
    (local : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (hSpan : HasSpanningRelation A)
    (oldColour : V → I)
    (hOldBlocks : ∀ x y : V,
      oldColour x ≠ oldColour y →
      x < y → oldColour x < oldColour y)
    (hLocalLinear : ∀ p, ALinear A (local p))
    (hLocalMono : ∀ p, ∀ a : Embedding A (local p),
      StrictMono a)
    (hLocalCovered : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : Embedding A (local p), x ∈ copyCarrier a)
    (hNonempty : Nonempty (FirstWagonUnionVertex oldCarrier))
    [Fintype κ] [Nonempty κ] :
    let B := firstWagonDisjointUnion oldCarrier local
    letI : LinearOrder (FirstWagonUnionVertex oldCarrier) :=
      firstWagonUnionOrder oldCarrier oldColour
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X)
      (R : StructuralRamsey.Structure (closureLanguage L) X),
      ElementaryCAClass A R ∧
      (letI : LinearOrder X := o
       ∃ (U : SummandPrivateTemplate.MonotoneClosedChoice A B R →
          PrivateWagonInput V P X),
         ∃ (hTemplate : ∀ c, (U c).templateEdges =
              supportCopies A (closureRelReduct R)),
           (∀ c p, StrictMono ((U c).coordinate p)) ∧
           ∀ ρ : {e : Set X //
                   e ∈ supportCopies A (closureRelReduct R)} → κ,
             ∃ (c : SummandPrivateTemplate.MonotoneClosedChoice A B R)
               (colour : κ),
               ∀ p : P, ∀ e : {e : Set X //
                   e ∈ supportCopies A (closureRelReduct R)},
                 e ∈ selectedCommonEdges U
                   (supportCopies A (closureRelReduct R))
                   hTemplate c p → ρ e = colour) := by
  let B := firstWagonDisjointUnion oldCarrier local
  letI : LinearOrder (FirstWagonUnionVertex oldCarrier) :=
    firstWagonUnionOrder oldCarrier oldColour
  have hLinear : ALinear A B :=
    firstWagonDisjointUnion_aLinear A oldCarrier local
      hPositive hSpan hLocalLinear
  have hMono : ∀ a : Embedding A B, StrictMono a :=
    firstWagonDisjointUnion_allACopies_strictMono
      A oldCarrier local hPositive hSpan
      oldColour hOldBlocks hLocalMono
  have hAB : Nonempty (Embedding A B) :=
    firstWagonDisjointUnion_hasACopy
      A oldCarrier local hPositive hLocalCovered hNonempty
  let include : (p : P) → Embedding (local p) B :=
    fun p => firstWagonSummandEmbedding oldCarrier local hPositive p
  have hInclStrong : ∀ p : P, AStrong A B (copyCarrier (include p)) :=
    fun p => firstWagonSummandEmbedding_aStrong
      A oldCarrier local hPositive hSpan p
  have hInclMono : ∀ p : P, StrictMono (include p) :=
    fun p => firstWagonSummandEmbedding_strictMono
      oldCarrier local hPositive oldColour hOldBlocks p
  exact SummandPrivateTemplate.exists_colouredRamsey_monotoneUnequalSummands
    A B (irreducible_of_spanningRelation A hSpan)
      hLinear hMono hAB oldCarrier local
      include hInclStrong hInclMono hLocalCovered

end StructuralRamsey.Girth

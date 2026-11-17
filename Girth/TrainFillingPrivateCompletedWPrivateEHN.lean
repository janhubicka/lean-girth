import Girth.TrainFillingPrivateCompletedWOrderedEHN
import Girth.TrainFillingPrivateMonotoneExistence

set_option Elab.async false

/-!
# The correct COMPLETED-W private EHN selection for unequal first wagons

The first input W of the manuscript is NOT the raw relational
coproduct. It has componentwise k-hyperedges and a FULL
within-colour binary order comparing vertices of all wagons.

We now derive all input hypotheses of the already prepared
unequal-summand ordered-EHN theorem for THIS W:
- each induced local F_p embeds inducedly in completed W,
- each inclusion is A-strong and strictly increasing,
- A-support is componentwise and A-linear,
- all A-embeddings in W are strictly increasing,
- local first wagons are A-covered, so a nonempty W contains A,
- A is the spanning-relationship small k-edge type.

This is still the RAW closure-EHN output on X, with an actual
monotone selected W-copy and a common monochromatic small-edge
support family. The full covered, marked and completed binary
order conversion of X is a separate Track 1 requirement.

Proof candidate, exact-head Lean kernel/axiom verification pending.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Girth.IndexedPrivateChoice

universe u v w
variable {I : Type u} {V P : Type v}
variable [LinearOrder I] [LinearOrder V] [LinearOrder P]
variable [Finite V] [Finite P]

/-- Genuine ordered EHN produces unequal first-wagon private
templates from ONE selected copy of the COMPLETED ordered W.
No F_p≃W, synthetic hBlin, hIncludeStrong or hIncludeMono
is assumed.

The old V-colour-block order is a chosen presentation order,
not the stronger and generally false assertion that V already
has a canonical total order across distinct predicates. -/
theorem completedFirstWagon_privateEHN
    {κ : Type w}
    (k : ℕ) (hk : 2 ≤ k)
    (profile : Fin k → I)
    (hProfileBlocks : ∀ i j : Fin k,
      i < j → profile i ≠ profile j → profile i < profile j)
    (oldEdges : Set (Set V)) (colour : V → I)
    (carrier : P → Set V)
    (hOldBlocks : ∀ x y : V,
      colour x ≠ colour y → x < y → colour x < colour y)
    (hOriginalLinear :
      ALinear (colouredOrderedEdgeSource.{u,v} k profile)
        (colouredOrderedEdgeTarget k oldEdges colour))
    (hLocalCovered : ∀ p : P, ∀ x : {v : V // v ∈ carrier p},
      ∃ a : Embedding (colouredOrderedEdgeSource.{u,v} k profile)
        ((colouredOrderedEdgeTarget k oldEdges colour).induce
          (carrier p)), x ∈ copyCarrier a)
    (hNonemptyW : Nonempty (FirstWagonUnionVertex carrier))
    [Fintype κ] [Nonempty κ] :
    let A := colouredOrderedEdgeSource.{u,v} k profile
    let D := colouredOrderedEdgeTarget k oldEdges colour
    let B := completedFirstWagonColouredUnion
      k oldEdges colour carrier
    letI : LinearOrder (FirstWagonUnionVertex carrier) :=
      firstWagonUnionOrder carrier colour
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X)
      (R : StructuralRamsey.Structure
        (closureLanguage (colouredOrderedEdgeLanguage I k)) X),
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
               (selectedColour : κ),
               ∀ p : P, ∀ e : {e : Set X //
                   e ∈ supportCopies A (closureRelReduct R)},
                 e ∈ selectedCommonEdges U
                   (supportCopies A (closureRelReduct R))
                   hTemplate c p → ρ e = selectedColour) := by
  classical
  let A := colouredOrderedEdgeSource.{u,v} k profile
  let D := colouredOrderedEdgeTarget k oldEdges colour
  let B := completedFirstWagonColouredUnion
    k oldEdges colour carrier
  letI : LinearOrder (FirstWagonUnionVertex carrier) :=
    firstWagonUnionOrder carrier colour
  let local : (p : P) →
      RelStructure (colouredOrderedEdgeLanguage I k)
        {v : V // v ∈ carrier p} :=
    fun p => D.induce (carrier p)
  let include : (p : P) → Embedding (local p) B :=
    fun p => completedFirstWagonSummandEmbedding
      k hk oldEdges colour carrier p
  have hLin : ALinear A B := by
    apply completedFirstWagon_aLinear
      k hk profile oldEdges colour carrier
    intro p
    exact aLinear_induce hOriginalLinear (carrier p)
  have hMono : ∀ a : Embedding A B, StrictMono a :=
    completedFirstWagon_allACopies_strictMono
      k profile hProfileBlocks oldEdges colour carrier
  have hSpan : HasSpanningRelation A :=
    colouredOrderedEdgeSource_hasSpanningRelation k profile
  have hIrred : A.Irreducible :=
    irreducible_of_spanningRelation A hSpan
  have hStrong : ∀ p : P,
      AStrong A B (copyCarrier (include p)) :=
    fun p => completedFirstWagonSummand_aStrong
      k hk profile oldEdges colour carrier p
  have hIncMono : ∀ p : P, StrictMono (include p) :=
    fun p => completedFirstWagonSummand_strictMono
      k hk oldEdges colour carrier hOldBlocks p
  have hAB : Nonempty (Embedding A B) := by
    obtain ⟨⟨p,x⟩⟩ := hNonemptyW
    obtain ⟨a, _hx⟩ := hLocalCovered p x
    exact ⟨(include p).comp a⟩
  exact SummandPrivateTemplate.exists_colouredRamsey_monotoneUnequalSummands
    A B hIrred hLin hMono hAB
    carrier local include hStrong hIncMono hLocalCovered

end StructuralRamsey.Girth

import Girth.TrainFillingPrivateCompletedWPrivateEHN
import Girth.TrainFillingPrivateActualFirstWagonSource

set_option Elab.async false

/-!
# Completed first-wagon EHN input DIRECTLY from original T

The original coloured-edge train has a genuine physical
edge type E(T) = full small-A support and its first-wagon
owner at level mu is the quotient [e]_mu.

From the OLD train alone we obtain:
- P = E(T)/~_mu, the exact actual wagon labels;
- oldCarrier(p) = union of all complete physical edges in p;
- local A-coverage of the induced F_p from original edge ownership;
- nonemptiness of W from one actual original physical edge;
- pairwise first-wagon carrier linearity from labelled girth >g>=2.

The COMPLETED W (not the raw relational coproduct) inherits
A-linearity and the ordered EHN copy properties. One selected
W-copy therefore gives all heterogeneous first-wagon extensions
and the common selected-edge colouring arrow.

This is the genuine source-side first EHN adapter for cutoff two.
Its EHN output X is still the raw functional closure witness,
not the final covered/marked ordered coloured-edge witness.
Track 1 must supply that conversion, and the shorter RR_h
OrderStage remains an independent induction hypothesis.

Source-only candidate pending exact-head Lean verification.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Girth.IndexedPrivateChoice

universe u v w
variable {I : Type u} {V : Type v}
variable [LinearOrder I] [LinearOrder V] [Finite V]

/-- The actual labelled first-wagon quotient of the original
T supplies the entire COMPLETED ordered W private Ramsey
family, with no arbitrary owner or local coverage premise.
The first-tail bound also returns its genuine carrier
linearity, used later in the private contraction. -/
theorem actualFirstWagonCompletedW_privateEHN
    {κ : Type w}
    (k : ℕ) (hk : 2 ≤ k)
    (profile : Fin k → I)
    (hProfileBlocks : ∀ i j : Fin k,
      i < j → profile i ≠ profile j → profile i < profile j)
    (oldEdges : Set (Set V)) (colour : V → I)
    (hOldBlocks : ∀ x y : V,
      colour x ≠ colour y → x < y → colour x < colour y)
    (hOldLinear :
      ALinear (colouredOrderedEdgeSource.{u,v} k profile)
        (colouredOrderedEdgeTarget k oldEdges colour))
    {m : ℕ}
    (T : EdgeTrainLevels
      {e : Set V // e ∈ supportCopies
        (colouredOrderedEdgeSource.{u,v} k profile)
        (colouredOrderedEdgeTarget k oldEdges colour)} m)
    (μ : Fin (m + 1))
    (g : ℕ) (hg : 2 ≤ g)
    (hGirth : LabelledGirthGT
      (T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies
          (colouredOrderedEdgeSource.{u,v} k profile)
          (colouredOrderedEdgeTarget k oldEdges colour)} => e.1)
        μ) g)
    (hNonemptyEdge : Nonempty
      {e : Set V // e ∈ supportCopies
        (colouredOrderedEdgeSource.{u,v} k profile)
        (colouredOrderedEdgeTarget k oldEdges colour)})
    [Fintype κ] [Nonempty κ] :
    let A := colouredOrderedEdgeSource.{u,v} k profile
    let D := colouredOrderedEdgeTarget k oldEdges colour
    let P := Quotient (T.wagonSetoid μ)
    let carrier : P → Set V :=
      T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ
    letI : LinearOrder P := T.wagonQuotientLinearOrder μ
    let B := completedFirstWagonColouredUnion
      k oldEdges colour carrier
    letI : LinearOrder (FirstWagonUnionVertex carrier) :=
      firstWagonUnionOrder carrier colour
    (∀ p q : P, p ≠ q →
      (carrier p ∩ carrier q).Subsingleton) ∧
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
  let E := {e : Set V // e ∈ supportCopies A D}
  let P := Quotient (T.wagonSetoid μ)
  let edgeCarrier : E → Set V := fun e => e.1
  let carrier : P → Set V := T.wagonClassCarrier edgeCarrier μ
  letI : Finite E := inferInstance
  letI : LinearOrder P := T.wagonQuotientLinearOrder μ
  have hFirst :=
    T.actualWagon_EHN_source_of_bound A D μ g hg hGirth
  have hCarrierLinear :
      ∀ p q : P, p ≠ q →
        (carrier p ∩ carrier q).Subsingleton :=
    hFirst.1
  have hLocalCovered : ∀ p : P,
      ∀ x : {v : V // v ∈ carrier p},
      ∃ a : Embedding A (D.induce (carrier p)),
        x ∈ copyCarrier a := hFirst.2
  have hPos : 0 < k := by omega
  letI : Nonempty (ULift.{v} (Fin k)) :=
    ⟨ULift.up (⟨0, hPos⟩ : Fin k)⟩
  have hNonemptyW :
      Nonempty (FirstWagonUnionVertex carrier) :=
    T.actualSupportWagonUnion_nonempty A D μ hNonemptyEdge
  refine ⟨hCarrierLinear, ?_⟩
  exact completedFirstWagon_privateEHN
    k hk profile hProfileBlocks oldEdges colour carrier
    hOldBlocks hOldLinear hLocalCovered hNonemptyW

end StructuralRamsey.Girth

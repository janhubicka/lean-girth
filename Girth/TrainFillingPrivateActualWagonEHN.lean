import Girth.TrainFillingPrivateRealColouredEHN
import Girth.TrainFillingPrivateActualFirstWagonSource

set_option Elab.async false

/-!
# Apply ordered EHN directly to the original labelled first-wagon quotient

The actual input of cutoff two is the ORIGINAL train T, on
the complete coloured A-support edge type of D.

At an old cut μ, the first-wagon labels are not an arbitrary P:
  P = Quotient (T.wagonSetoid μ).
Their carriers are the actual complete union of their
physical edges, and the owner of every old A-edge is its
own quotient class. The checked wagonClassCarrier API and
our Track 5 quotient lemmas give ALL owner, local cover
and first-wagon linearity facts, the last from the paper's
labelled girth bound > h_1 with h_1 >= 2.

The quotient is finite whenever the original target is finite,
so its auxiliary order is CONSTRUCTED, not an external input.
Nonemptiness of W follows from an actual old A-edge.

Consequently the concrete realColouredFirstWagon_privateEHN
existence theorem can be invoked directly on the old train,
with no arbitrary wagon-owner function, foreign first-wagon
coverage, separate first-wagon carrier linearity, or invented
choice of a first-wagon label order.

The resulting X is the RAW functional EHN template.
Making it covered and imposing the allowed A_1 overlap
predicates is the separate Track 1 owner-splitting interface,
and is NOT claimed here. The actual shortened M and RR_h
selected OrderStage remain the next Track 5 application.

Proof candidate until exact-head Lean elaboration and
#print axioms. No new axiom, sorry or girth hypothesis.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Girth.IndexedPrivateChoice

universe u v w

variable {I : Type u} {V : Type v}
variable [LinearOrder I] [LinearOrder V] [Finite V]

/-- Actual original coloured train, with TRUE first-wagon quotient
labels and the paper's own >g wagon girth, produces the entire
unequal-summand ordered EHN private choice family.

This is the first genuine outer-stage existence adapter:
the input is a single EdgeTrainLevels T, not separately
constructed local wagon structures and an arbitrary owner map.

The explicitly retained assumptions are exactly old
coloured-edge A-linearity/order, a nonempty old edge,
the labelled first-wagon girth bound >g>=2,
and the finite colouring. -/
theorem actualFirstWagonQuotient_privateEHN
    {κ : Type w}
    (k : ℕ) (hk : 2 ≤ k)
    (profile : Fin k → I)
    (hProfileBlocks : ∀ i j : Fin k,
      i < j → profile i ≠ profile j → profile i < profile j)
    (E : Set (Set V)) (oldColour : V → I)
    (hOldBlocks : ∀ x y : V,
      oldColour x ≠ oldColour y →
      x < y → oldColour x < oldColour y)
    (hOldColourToOrder : ∀ x y : V,
      oldColour x < oldColour y → x < y)
    (hOldLinear :
      ALinear (colouredOrderedEdgeSource.{u,v} k profile)
        (colouredOrderedEdgeTarget k E oldColour))
    {m : ℕ}
    (T : EdgeTrainLevels
      {e : Set V // e ∈ supportCopies
        (colouredOrderedEdgeSource.{u,v} k profile)
        (colouredOrderedEdgeTarget k E oldColour)} m)
    (μ : Fin (m + 1))
    (g : ℕ) (hg : 2 ≤ g)
    (hWagonGirth : LabelledGirthGT
      (T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies
          (colouredOrderedEdgeSource.{u,v} k profile)
          (colouredOrderedEdgeTarget k E oldColour)} => e.1)
        μ) g)
    (hNonemptySupport : Nonempty
      {e : Set V // e ∈ supportCopies
        (colouredOrderedEdgeSource.{u,v} k profile)
        (colouredOrderedEdgeTarget k E oldColour)})
    [Fintype κ] [Nonempty κ] :
    let A := colouredOrderedEdgeSource.{u,v} k profile
    let D := colouredOrderedEdgeTarget k E oldColour
    let P := Quotient (T.wagonSetoid μ)
    let oldCarrier : P → Set V :=
      T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ
    letI : LinearOrder P := T.wagonQuotientLinearOrder μ
    let B := firstWagonDisjointUnion oldCarrier
      (fun p => D.induce (oldCarrier p))
    letI : LinearOrder (FirstWagonUnionVertex oldCarrier) :=
      firstWagonUnionOrder oldCarrier oldColour
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
               (colour : κ),
               ∀ p : P, ∀ e : {e : Set X //
                   e ∈ supportCopies A (closureRelReduct R)},
                 e ∈ selectedCommonEdges U
                   (supportCopies A (closureRelReduct R))
                   hTemplate c p → ρ e = colour) := by
  classical
  let A := colouredOrderedEdgeSource.{u,v} k profile
  let D := colouredOrderedEdgeTarget k E oldColour
  let OldEdge := {e : Set V // e ∈ supportCopies A D}
  let P := Quotient (T.wagonSetoid μ)
  let oldEdges : OldEdge → Set V := fun e => e.1
  let oldCarrier : P → Set V := T.wagonClassCarrier oldEdges μ
  let owner : OldEdge → P := T.wagonClassOwner μ
  letI : Finite (Set V) := inferInstance
  letI : Finite OldEdge := inferInstance
  letI : LinearOrder P := T.wagonQuotientLinearOrder μ
  have hPositive : 0 < k := by omega
  letI : Nonempty (ULift.{v} (Fin k)) :=
    ⟨ULift.up (⟨0, hPositive⟩ : Fin k)⟩
  have hOwnerCarrier : ∀ e : OldEdge,
      e.1 ⊆ oldCarrier (owner e) := by
    intro e
    exact T.edge_subset_ownerWagonCarrier oldEdges μ e
  have hCover : ∀ (p : P)
      (x : {v : V // v ∈ oldCarrier p}),
        ∃ e : OldEdge, owner e = p ∧ x.1 ∈ e.1 := by
    intro p x
    exact T.ownerEdge_covers_wagonVertex oldEdges μ p x.1 x.2
  have hNonemptyW : Nonempty (FirstWagonUnionVertex oldCarrier) :=
    T.actualSupportWagonUnion_nonempty A D μ hNonemptySupport
  exact realColouredFirstWagon_privateEHN k hk profile
    hProfileBlocks E oldColour hOldBlocks hOldColourToOrder
    hOldLinear oldCarrier owner hOwnerCarrier hCover hNonemptyW

end StructuralRamsey.Girth

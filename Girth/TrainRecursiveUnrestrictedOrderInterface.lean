import Girth.TrainRecursiveUniformAllInputs
import Girth.TrainRecursiveOneEdgeDichotomy

set_option autoImplicit false
set_option Elab.async false

/-!
# The genuinely unrestricted order input needed at cutoff two

The shorter train in the manuscript is of a NEW coloured edge type X
(possibly with repeated coarse vertex predicates). It is not generally
X-partite: different X coordinates on two first-wagon edges can be
identified at an original common vertex.

Hence UniformSelectedPartiteOrderAllInputs, despite its correct type
and palette quantifiers, is insufficient as the RR_tail input.

The order assertion below quantifies over an ARBITRARY finite ordered
target train B, without any B.IsPartiteOver A assumption or any global
part map on B indexed by the vertices of its edge type A. Its output
is allowed to be partite over the entire target B; this is the ordinary
picture setup, distinct from assuming that B itself is A-partite.

This corrects the type of the order field in the abstract rank
operators. Nothing here proves the general forest-to-order transfer
or the cutoff-two filling step. The still-needed theorems remain
explicit inputs to the conditional operators.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {UA VB : Type v}

/-- An unrestricted selected order-Ramsey assertion at a given vector,
for every finite ordered edge type, arbitrary finite ordered target
and finite nonempty palette. No global A-part map on the target B is
present in the input.

The output is an actual OrderStage with full system-girth at all cuts
and a real selected DesignatedArrow; it is based over B using the
singleton identity base family. The B-partite output is not a
hypothesis that the INPUT B is A-partite. -/
def UniformSelectedUnrestrictedOrderAllInputs
    (L : RelLanguage.{u}) (t : List ℕ) : Prop :=
  ∀ {UA : Type v} [LinearOrder UA] [Finite UA] [Nonempty UA]
    (A₀ : RelStructure L UA)
    (κ : Type) [Fintype κ] [Nonempty κ]
    {VB : Type v} [Finite VB]
    (B : RelStructure L.withOrder VB)
    (ht : Admissible t)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) t.length)
    (allowed : Fin (t.length + 1) → Set VB)
    (hSupportNonempty : Nonempty
      (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ x : VB,
      ∃ a : OldACarrierEdge A₀.ordered B, x ∈ a.1)
    (hGirth : GirthGT
      (supportCopies A₀.ordered B) (t.headD 0))
    (hParameters : targetTrain.AdjacentParameters
      (fun e => e.1) allowed)
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun e => e.1) j.castSucc)
        (t.get j)),
    ∃ S : OrderStage A₀.ordered B B
        {Embedding.id B} t targetTrain allowed,
      DesignatedArrow S.toForestTailStage κ

/-- The already checked one-physical-edge result really is a member
of this NONPARTITE order domain: no B-to-A part map is assumed and
the conclusion uses the actual original train and base B. -/
theorem unrestrictedOrder_oneEdge_case
    {L : RelLanguage.{u}}
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) t.length)
    (allowed : Fin (t.length + 1) → Set VB)
    (hSupportNonempty : Nonempty (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ x : VB,
      ∃ a : OldACarrierEdge A₀.ordered B, x ∈ a.1)
    (κ : Type w)
    (hNoTwo : ¬ ∃ a b : Embedding A₀.ordered B,
      ¬ SameCopy a b) :
    ∃ S : OrderStage A₀.ordered B B
        {Embedding.id B} t targetTrain allowed,
      DesignatedArrow S.toForestTailStage κ :=
  exists_orderStage_of_no_two_copies
    A₀ B t ht targetTrain allowed
    hSupportNonempty hSupportCovers κ hNoTwo

/-- Correct mixed operator contract: the q>2 partite forest step is
already proved, but SAME-VECTOR forest-to-order must produce an
UNRESTRICTED order witness before cutoff two can consume it.
The two fields are mathematical obligations, not instance fields
filled by a partite-only order theorem. -/
def uniformSelectedUnrestrictedOperators
    (L : RelLanguage.{u})
    (baseTwo : UniformSelectedPartiteForestAllInputs.{u, v} L [2])
    (forestToUnrestrictedOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForestAllInputs.{u, v} L t →
      UniformSelectedUnrestrictedOrderAllInputs.{u, v} L t)
    (cutoffTwo : ∀ tail, Admissible tail →
      UniformSelectedUnrestrictedOrderAllInputs.{u, v} L tail →
      UniformSelectedPartiteForestAllInputs.{u, v} L (2 :: tail)) :
    Operators
      (UniformSelectedPartiteForestAllInputs.{u, v} L)
      (UniformSelectedUnrestrictedOrderAllInputs.{u, v} L) where
  baseTwo := baseTwo
  forestToOrder := forestToUnrestrictedOrder
  cutoffTwo := cutoffTwo
  largerCutoff := by
    intro q tail _ hq hAllLower
    exact uniformSelectedPartiteForestAllInputs_largerCutoff
      L q tail hq hAllLower

/-- Full rank assembly, CONDITIONAL on the three genuine unproved
operators. In particular no partite-order statement is substituted
for the arbitrary shorter-train RR_tail premise. -/
theorem uniformSelectedPartiteForest_of_correctOrderOperators
    (L : RelLanguage.{u})
    (baseTwo : UniformSelectedPartiteForestAllInputs.{u, v} L [2])
    (forestToUnrestrictedOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForestAllInputs.{u, v} L t →
      UniformSelectedUnrestrictedOrderAllInputs.{u, v} L t)
    (cutoffTwo : ∀ tail, Admissible tail →
      UniformSelectedUnrestrictedOrderAllInputs.{u, v} L tail →
      UniformSelectedPartiteForestAllInputs.{u, v} L (2 :: tail))
    (t : List ℕ) (ht : Admissible t) :
    UniformSelectedPartiteForestAllInputs.{u, v} L t :=
  (uniformSelectedUnrestrictedOperators L baseTwo
    forestToUnrestrictedOrder cutoffTwo).assemble t ht

end StructuralRamsey.Girth.TrainRecursiveWitness

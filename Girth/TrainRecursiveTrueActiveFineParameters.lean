import Girth.TrainRecursiveTrueActiveAdjacentParameters
import Girth.TrainRecursiveRefinementForwardParameters
import Girth.TrainRecursiveCanonicalFineAllowed

set_option autoImplicit false
set_option Elab.async false

/-!
# Complete fine-target adjacent parameters on the TRUE active source

This is the actual q>2 combination, without a fresh independent
fine AdjacentParameters premise.

First retain the complete old-stage adjacent sibling bounds on all
shared physical old A-edges.  The genuine FirstWagonRefinement then
constructs the full fine sibling bounds: its own R.parameters handles
every inserted cut, including the first retained parent, while the
exact old train handles all later retained cuts.

Finally transport the ENTIRE fine train, not a selected edge subfamily,
along the bijection between shared old support and the induced active
A-support.  The injective vertex map is the subtype inclusion.  The
canonical fine allowed parts are exactly the preimages prescribed by
fineAllowedFromRefinement; the old P-coordinate equals alpha of the
active A-coordinate on each genuine active vertex.

No Hales--Jewett girth assertion, lower recursive witness, full-system
girth, or output SupremeCycleBound is claimed.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- Complete TRUE active fine target adjacent parameters, including the
physical equality cut, every newly inserted refinement parent, the
overlapping first retained parent, and every later retained parent.
The allowed A-parts are the existing canonical fineAllowedFromRefinement
from the actual original refinement's permitted singleton part sets. -/
theorem ForestTailStage.trueActive_inducedRefinementAdjacentParameters
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D) (hm : 0 < t.length) {g : ℕ}
    (R : FirstWagonRefinement
      (stage.train.restrict
        (sharedOldACarrierInclusion A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding)))
      hm
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
      stage.system.part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩) g) :
    (R.train.restrict
      (inducedACarrierToShared A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding))).AdjacentParameters
      (fun edge : OldACarrierEdge A
        (stage.system.toRelStructure.induce
          (activeCarrier A stage.system e.toFunctionEmbedding)) => edge.1)
      (fun ρ =>
        (actualActiveSubsystemPartite A stage.system
          e.toFunctionEmbedding).part ⁻¹'
          (fineAllowedFromRefinement t.length R.extraCuts hm
            e.toFunctionEmbedding allowed R.permitted ρ)) := by
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  let α := e.toFunctionEmbedding
  let Tshared := stage.train.restrict
    (sharedOldACarrierInclusion A stage.system.toRelStructure S)
  let oldFine : Fin (t.length + R.extraCuts + 1) → Set P :=
    fineAllowedFromRefinement t.length R.extraCuts hm
      (Function.Embedding.refl P) allowed R.permitted
  have hOldFineInserted (j : Fin (R.extraCuts + 1)) :
      oldFine (firstRefinementParent t.length R.extraCuts hm j) =
        R.permitted j := by
    change fineAllowedFromRefinement t.length R.extraCuts hm
      (Function.Embedding.refl P) allowed R.permitted
      (firstRefinementParent t.length R.extraCuts hm j) = R.permitted j
    rw [fineAllowedFromRefinement_parent]
    rfl
  have hOldFineRetained (ν : Fin (t.length + 1))
      (hν : 1 < ν.val) :
      oldFine (EdgeTrainLevels.firstForgetIndex t.length R.extraCuts ν) =
        allowed ν := by
    change fineAllowedFromRefinement t.length R.extraCuts hm
      (Function.Embedding.refl P) allowed R.permitted
      (EdgeTrainLevels.firstForgetIndex t.length R.extraCuts ν) =
      allowed ν
    rw [fineAllowedFromRefinement_retained_gt_one
      t.length R.extraCuts hm (Function.Embedding.refl P)
      allowed R.permitted ν hν]
    rfl
  have hPreimage (ρ : Fin (t.length + R.extraCuts + 1)) :
      α ⁻¹' oldFine ρ =
        fineAllowedFromRefinement t.length R.extraCuts hm
          α allowed R.permitted ρ := by
    ext x
    by_cases h : 0 < ρ.val ∧ ρ.val ≤ R.extraCuts + 1
    · simp only [oldFine, fineAllowedFromRefinement, dif_pos h]
      rfl
    · simp only [oldFine, fineAllowedFromRefinement, dif_neg h]
      rfl
  have hShared : Tshared.AdjacentParameters
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S =>
        edge.1.1)
      (fun ν => stage.system.part ⁻¹' allowed ν) := by
    apply stage.train.adjacentParameters_restrict_of_vertexEmbedding
      (fun edge : OldACarrierEdge A stage.system.toRelStructure => edge.1)
      (sharedOldACarrierInclusion A stage.system.toRelStructure S)
      (Function.Embedding.refl stage.Vertex)
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S =>
        edge.1.1)
      (by intro edge x hx; exact hx)
      (fun ν => stage.system.part ⁻¹' allowed ν)
      (fun ν => stage.system.part ⁻¹' allowed ν)
      (by intro ν x hx; exact hx)
      stage.parameters
  have hFineShared : R.train.AdjacentParameters
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S =>
        edge.1.1)
      (fun ρ => stage.system.part ⁻¹' oldFine ρ) := by
    apply R.adjacentParameters_of_old
      (fun ν => stage.system.part ⁻¹' allowed ν)
      (fun ρ => stage.system.part ⁻¹' oldFine ρ) hShared
    · intro j
      rw [hOldFineInserted j]
    · intro ν hν
      rw [hOldFineRetained ν hν]
  change (R.train.restrict
      (inducedACarrierToShared A stage.system.toRelStructure S)).AdjacentParameters
      (fun edge : OldACarrierEdge A (stage.system.toRelStructure.induce S) =>
        edge.1)
      (fun ρ =>
        (actualActiveSubsystemPartite A stage.system α).part ⁻¹'
          (fineAllowedFromRefinement t.length R.extraCuts hm
            α allowed R.permitted ρ))
  apply R.train.adjacentParameters_restrict_of_vertexEmbedding
    (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S =>
      edge.1.1)
    (inducedACarrierToShared A stage.system.toRelStructure S)
    (⟨Subtype.val, Subtype.val_injective⟩ : S ↪ stage.Vertex)
    (fun edge : OldACarrierEdge A (stage.system.toRelStructure.induce S) =>
      edge.1)
    (by
      intro edge x hx
      change x.val ∈ Subtype.val '' edge.1
      exact ⟨x, hx, rfl⟩)
    (fun ρ => stage.system.part ⁻¹' oldFine ρ)
    (fun ρ => (actualActiveSubsystemPartite A stage.system α).part ⁻¹'
      (fineAllowedFromRefinement t.length R.extraCuts hm
        α allowed R.permitted ρ))
    (by
      intro ρ x hx
      change activeSourcePart A stage.system α x ∈
        fineAllowedFromRefinement t.length R.extraCuts hm
          α allowed R.permitted ρ
      rw [← hPreimage ρ]
      change α (activeSourcePart A stage.system α x) ∈ oldFine ρ
      rw [activeSourcePart_spec A stage.system α x]
      exact hx)
    hFineShared

end StructuralRamsey.Girth.TrainRecursiveWitness

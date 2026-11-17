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
theorem trueActive_inducedRefinementAdjacentParameters_of_parameters
    {X : Type v} {m : ℕ} (C : StructuralRamsey.Partite.System L P X)
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
    (allowed : Fin (m + 1) → Set P)
    (hParameters : T.AdjacentParameters (fun edge => edge.1)
      (fun ν => C.part ⁻¹' allowed ν))
    (e : Embedding A D) (hm : 0 < m) {g : ℕ}
    (R : FirstWagonRefinement
      (T.restrict
        (sharedOldACarrierInclusion A C.toRelStructure
          (activeCarrier A C e.toFunctionEmbedding)))
      hm
      (fun edge : SharedOldACarrierEdge A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) => edge.1.1)
      C.part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩) g) :
    (R.train.restrict
      (inducedACarrierToShared A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding))).AdjacentParameters
      (fun edge : OldACarrierEdge A
        (C.toRelStructure.induce
          (activeCarrier A C e.toFunctionEmbedding)) => edge.1)
      (fun ρ =>
        (actualActiveSubsystemPartite A C
          e.toFunctionEmbedding).part ⁻¹'
          (fineAllowedFromRefinement m R.extraCuts hm
            e.toFunctionEmbedding allowed R.permitted ρ)) := by
  let S := activeCarrier A C e.toFunctionEmbedding
  let α := e.toFunctionEmbedding
  let Tshared := T.restrict
    (sharedOldACarrierInclusion A C.toRelStructure S)
  let oldFine : Fin (m + R.extraCuts + 1) → Set P :=
    fineAllowedFromRefinement m R.extraCuts hm
      (Function.Embedding.refl P) allowed R.permitted
  have hOldFineInserted (j : Fin (R.extraCuts + 1)) :
      oldFine (firstRefinementParent m R.extraCuts hm j) =
        R.permitted j := by
    change fineAllowedFromRefinement m R.extraCuts hm
      (Function.Embedding.refl P) allowed R.permitted
        (firstRefinementParent m R.extraCuts hm j) = R.permitted j
    rw [fineAllowedFromRefinement_parent]
    rfl
  have hOldFineRetained (ν : Fin (m + 1))
      (hν : 1 < ν.val) :
      oldFine (EdgeTrainLevels.firstForgetIndex m R.extraCuts ν) =
        allowed ν := by
    change fineAllowedFromRefinement m R.extraCuts hm
      (Function.Embedding.refl P) allowed R.permitted
        (EdgeTrainLevels.firstForgetIndex m R.extraCuts ν) = allowed ν
    rw [fineAllowedFromRefinement_retained_gt_one
      m R.extraCuts hm (Function.Embedding.refl P)
      allowed R.permitted ν hν]
    rfl
  have hPreimage (ρ : Fin (m + R.extraCuts + 1)) :
      α ⁻¹' oldFine ρ =
        fineAllowedFromRefinement m R.extraCuts hm
          α allowed R.permitted ρ := by
    ext x
    by_cases h : 0 < ρ.val ∧ ρ.val ≤ R.extraCuts + 1
    · simp only [oldFine, fineAllowedFromRefinement, dif_pos h]
      rfl
    · simp only [oldFine, fineAllowedFromRefinement, dif_neg h]
      rfl
  have hShared : Tshared.AdjacentParameters
      (fun edge : SharedOldACarrierEdge A C.toRelStructure S =>
        edge.1.1)
      (fun ν => C.part ⁻¹' allowed ν) := by
    apply T.adjacentParameters_restrict_of_vertexEmbedding
      (fun edge : OldACarrierEdge A C.toRelStructure => edge.1)
      (sharedOldACarrierInclusion A C.toRelStructure S)
      (Function.Embedding.refl X)
      (fun edge : SharedOldACarrierEdge A C.toRelStructure S =>
        edge.1.1)
      (by intro edge x hx; exact hx)
      (fun ν => C.part ⁻¹' allowed ν)
      (fun ν => C.part ⁻¹' allowed ν)
      (by intro ν x hx; exact hx)
      hParameters
  have hFineShared : R.train.AdjacentParameters
      (fun edge : SharedOldACarrierEdge A C.toRelStructure S =>
        edge.1.1)
      (fun ρ => C.part ⁻¹' oldFine ρ) := by
    apply R.adjacentParameters_of_old
      (fun ν => C.part ⁻¹' allowed ν)
      (fun ρ => C.part ⁻¹' oldFine ρ) hShared
    · intro j
      rw [hOldFineInserted j]
    · intro ν hν
      rw [hOldFineRetained ν hν]
  change (R.train.restrict
      (inducedACarrierToShared A C.toRelStructure S)).AdjacentParameters
      (fun edge : OldACarrierEdge A (C.toRelStructure.induce S) =>
        edge.1)
      (fun ρ =>
        (actualActiveSubsystemPartite A C α).part ⁻¹'
          (fineAllowedFromRefinement m R.extraCuts hm
            α allowed R.permitted ρ))
  apply R.train.adjacentParameters_restrict_of_vertexEmbedding
    (fun edge : SharedOldACarrierEdge A C.toRelStructure S =>
      edge.1.1)
    (inducedACarrierToShared A C.toRelStructure S)
    (⟨Subtype.val, Subtype.val_injective⟩ : S ↪ X)
    (fun edge : OldACarrierEdge A (C.toRelStructure.induce S) =>
      edge.1)
    (by
      intro edge x hx
      change x.val ∈ Subtype.val '' edge.1
      exact ⟨x, hx, rfl⟩)
    (fun ρ => C.part ⁻¹' oldFine ρ)
    (fun ρ => (actualActiveSubsystemPartite A C α).part ⁻¹'
      (fineAllowedFromRefinement m R.extraCuts hm
        α allowed R.permitted ρ))
    (by
      intro ρ x hx
      change activeSourcePart A C α x ∈
        fineAllowedFromRefinement m R.extraCuts hm
          α allowed R.permitted ρ
      rw [← hPreimage ρ]
      change α (activeSourcePart A C α x) ∈ oldFine ρ
      rw [activeSourcePart_spec A C α x]
      exact hx)
    hFineShared


/-- The original selected stage supplies the ambient parameters. -/
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
            e.toFunctionEmbedding allowed R.permitted ρ)) :=
  trueActive_inducedRefinementAdjacentParameters_of_parameters stage.system
    stage.train allowed stage.parameters e hm R

end StructuralRamsey.Girth.TrainRecursiveWitness

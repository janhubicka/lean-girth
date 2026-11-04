import Girth.TrainRecursiveInitialTargetStage
import Girth.TrainRecursiveLargeBaseCoarsening

set_option autoImplicit false
set_option Elab.async false

/-!
# Initial forest stage over a larger partite base: one target parameter bound suffices

The actual initial-stage constructor originally asks for the target
train's adjacent-parameter estimate after pulling the allowed BASE
sets back through every designated embedding B -> D. For the positive
larger-base repair, D is genuinely A-partite, every family member
preserves A-parts, and the lower base allowed set is the inverse image
of one fine A-part set.

In this case every such pullback is LITERALLY the same A-part
predicate on the original target. Thus a SINGLE source-train parameter
bound constructs the full initial forest-tail stage, without
postulating independent compatibility for the members of the HJ line
family. The physical edge/train family is unchanged.

This is initial-stage construction, not the complete recursive witness:
the target's support girth, labelled positive cut girths and the
finite picture-step operator remain genuine separate obligations.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- A part-preserving family has exactly the same pulled-back allowed
sets at every target copy when the larger base allowed sets are
preimages along the base part map. In particular the lower initial
stage needs only ONE adjacent-parameter hypothesis on the target. -/
theorem targetParameters_of_partiteFamily_preimage
    (A : RelStructure L UA)
    (Target : StructuralRamsey.Partite.System L UA VB)
    (D : StructuralRamsey.Partite.System L UA P)
    (family : Set (Embedding Target.toRelStructure D.toRelStructure))
    (hParts : ∀ b, b ∈ family → ∀ x : VB,
      D.part (b x) = Target.part x)
    {t : List ℕ}
    (train : EdgeTrainLevels (OldACarrierEdge A Target.toRelStructure) t.length)
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (hTarget : train.AdjacentParameters (fun edge => edge.1)
      (fun ν => Target.part ⁻¹' fineAllowed ν)) :
    ∀ b : family,
      train.AdjacentParameters (fun edge => edge.1)
        (fun ν => b.1 ⁻¹' (D.part ⁻¹' fineAllowed ν)) := by
  intro b
  have hSets :
      (fun ν => b.1 ⁻¹' (D.part ⁻¹' fineAllowed ν)) =
      (fun ν => Target.part ⁻¹' fineAllowed ν) := by
    funext ν
    ext x
    change D.part (b.1 x) ∈ fineAllowed ν ↔
      Target.part x ∈ fineAllowed ν
    rw [hParts b.1 b.2 x]
  rw [hSets]
  exact hTarget

/-- A concrete initial lower ForestTailStage over ANY finite larger
A-partite Ramsey base and part-preserving family, with allowed base
sets chosen as the exact preimages of the desired A-part sets.

Only the intrinsic TARGET train parameter condition is needed, not
one condition for each prescribed large-base embedding. The
initial tail full-system bounds come from target labelled cuts via
the existing actual initial-tail constructor. -/
noncomputable def initialForestTailStage_of_partiteBaseTargetCuts
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (Target : StructuralRamsey.Partite.System L UA VB) [Finite VB]
    (D : StructuralRamsey.Partite.System L UA P) [Finite P]
    (family : Set (Embedding Target.toRelStructure D.toRelStructure))
    [Nonempty family]
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
      D.part (b x) = Target.part x)
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A Target.toRelStructure) t.length)
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (hSupportNonempty : Nonempty (OldACarrierEdge A Target.toRelStructure))
    (hSupportCovers : ∀ b : VB,
      ∃ e : OldACarrierEdge A Target.toRelStructure, b ∈ e.1)
    (hTargetGirth : GirthGT
      (supportCopies A Target.toRelStructure) (t.headD 0))
    (hTargetParameters : targetTrain.AdjacentParameters
      (fun edge => edge.1) (fun ν => Target.part ⁻¹' fineAllowed ν))
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        (t.get j)) :
    ForestTailStage A Target.toRelStructure D.toRelStructure
      family t targetTrain (fun ν => D.part ⁻¹' fineAllowed ν) :=
  initialForestTailStage_of_targetCuts
    A hA Target.toRelStructure D.toRelStructure family
    t ht targetTrain (fun ν => D.part ⁻¹' fineAllowed ν)
    hSupportNonempty hSupportCovers hTargetGirth
    (targetParameters_of_partiteFamily_preimage
      A Target D family hFamilyParts targetTrain fineAllowed hTargetParameters)
    hTargetCuts

end StructuralRamsey.Girth.TrainRecursiveWitness

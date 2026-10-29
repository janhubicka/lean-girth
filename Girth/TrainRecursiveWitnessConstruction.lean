import Girth.TrainRecursiveWitnessInitialStage
import Girth.TrainRecursiveWitnessProfiles

/-!
# Finite witness assembly from the actual initial picture

This theorem starts with the target data, constructs the genuine selected
initial forest/tail stage, enumerates all injective profiles, and applies
the strengthened finite pass.  An inhabited fibre realizes an actual base
embedding; an absent fibre uses the identity transition and the explicitly
supplied readiness-drop law.

The output is one actual finite stage carrying its selected Ramsey arrow,
strong selected target copies, exact target train, adjacent parameters,
bottom mixed forest and all tail bounds.  The supplied local operators
still have to construct the geometric nonempty-fibre steps.  The input
initialTail remains the exact initial-picture tail-cycle obligation; no
arbitrary initial stage or final witness-existence theorem is a hypothesis.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- Assemble the finite selected Ramsey witness from the actual initial
stage and actual-base-embedding local steps.  `DesignatedArrow.strongTrain`
extracts the resulting monochromatic strong train copy from this same stage.
-/
theorem constructFromInitial_of_actualSteps
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA] [Finite UA]
    (B : RelStructure L VB) [Finite VB]
    (D : RelStructure L P) [Finite P]
    (family : Set (RelStructure.Embedding B D)) [Nonempty family]
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ b : VB, ∃ e : OldACarrierEdge A B, b ∈ e.1)
    (hGirth : GirthGT (supportCopies A B) (t.headD 0))
    (hTargetParameters : ∀ b : family,
      targetTrain.AdjacentParameters (fun edge => edge.1)
        (fun ν => b.1 ⁻¹' allowed ν))
    (hInitialTail : ∀ j : Fin t.length, 0 < j.val →
      (selectedPictureOrderOneData A B D
        (StructuralRamsey.Partite.Initial.picture B
          (fun b : family => b.1.toFunctionEmbedding))
        family (initialSelected B D family)
        (initialTrain A hA B (fun b : family => b.1.toFunctionEmbedding)
          targetTrain (List.length_pos_iff.mpr ht.nonempty))
        j.castSucc).FullSystemGirthGT (t.get j))
    (κ : Type w) [Nonempty κ]
    (hBase : ∀ χ : RelStructure.Embedding A D → κ,
      ∃ b : RelStructure.Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : RelStructure.Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (Ready : List (UA ↪ P) →
      ForestTailStage A B D family t targetTrain allowed → Prop)
    (hReady : Ready (projectionProfileList UA P)
      (initialForestTailStage_of_tail A hA B D family t ht targetTrain allowed
        hSupportNonempty hSupportCovers hGirth hTargetParameters hInitialTail))
    (emptyReady : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (S : ForestTailStage A B D family t targetTrain allowed),
      Ready (α :: remaining) S →
      ¬ Nonempty (StructuralRamsey.Partite.ProjectedEmbedding A S.system α) →
        Ready remaining S)
    (actualStep : ∀ (e : RelStructure.Embedding A D)
      (remaining : List (UA ↪ P))
      (S : ForestTailStage A B D family t targetTrain allowed),
      Nonempty (StructuralRamsey.Partite.ProjectedEmbedding A S.system
        e.toFunctionEmbedding) →
      Ready (e.toFunctionEmbedding :: remaining) S →
        ∃ T : ForestTailStage A B D family t targetTrain allowed,
          Ready remaining T ∧ PictureStep S T e.toFunctionEmbedding κ) :
    ∃ T : ForestTailStage A B D family t targetTrain allowed,
      Ready [] T ∧ DesignatedArrow T κ := by
  let initial := initialForestTailStage_of_tail A hA B D family t ht
    targetTrain allowed hSupportNonempty hSupportCovers hGirth
    hTargetParameters hInitialTail
  have hLift : ∀ b : RelStructure.Embedding B D, b ∈ family →
      ∃ q : DesignatedCopy B D initial.system family,
        q ∈ initial.selected ∧ q.base = b := by
    intro b hb
    exact initialPicture_lifts B D family b hb
  apply ForestTailStage.ramseyPass initial (projectionProfileList UA P) κ
    Ready hReady (mem_projectionProfileList) hBase hLift
  intro α remaining S hReadyS
  exact ForestTailStage.profileStep_of_actualStep S hA α remaining κ Ready
    hReadyS (emptyReady α remaining S hReadyS)
    (fun e hFibre hReadyE => actualStep e remaining S hFibre hReadyE)

end StructuralRamsey.Girth.TrainRecursiveWitness

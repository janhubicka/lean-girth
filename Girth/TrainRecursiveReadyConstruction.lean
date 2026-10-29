import Girth.TrainRecursiveInitialTargetStage
import Girth.TrainRecursiveWitnessConstruction

/-!
# Selected witness construction from target cuts and concrete refinements

This endpoint removes the abstract initial-tail and readiness inputs from
the first finite-pass assembly.  The actual initial tail bounds follow from
the target's labelled horizontal cuts.  The complete initial active support
is a matching, so the initial stage has genuine finite first-wagon
refinements.  The concrete readiness predicate has a proved profile-drop
law, and the prescribed base Ramsey arrow supplies a nonempty base family.

The remaining local input constructs an inhabited-fibre picture step while
preserving precisely those refinements on the unprocessed fibres.  Its
existence, the larger-cutoff girth gain, and the cutoff-two filling step are
not asserted here.  Every output invariant is carried by the same finite
selected stage, including all ambient A-edges and every tail condition.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- Construct a finite selected strong train Ramsey witness from natural
target girth and actual nonempty-fibre steps preserving the concrete
first-wagon refinement invariant.  No initial output stage, output tail
bound, abstract readiness predicate, initial readiness proof, or empty-step
readiness premise is required. -/
theorem constructFromTargetCuts_of_refiningSteps
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA] [Finite UA]
    (B : RelStructure L VB) [Finite VB]
    (D : RelStructure L P) [Finite P]
    (family : Set (RelStructure.Embedding B D))
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ b : VB, ∃ e : OldACarrierEdge A B, b ∈ e.1)
    (hGirth : GirthGT (supportCopies A B) (t.headD 0))
    (hTargetParameters : ∀ b : family,
      targetTrain.AdjacentParameters (fun edge => edge.1)
        (fun ν => b.1 ⁻¹' allowed ν))
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        (t.get j))
    (refinementBudget : ℕ)
    (κ : Type w) [Nonempty κ]
    (hBase : ∀ χ : RelStructure.Embedding A D → κ,
      ∃ b : RelStructure.Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : RelStructure.Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (actualStep : ∀ (e : RelStructure.Embedding A D)
      (remaining : List (UA ↪ P))
      (S : ForestTailStage A B D family t targetTrain allowed),
      Nonempty (StructuralRamsey.Partite.ProjectedEmbedding A S.system
        e.toFunctionEmbedding) →
      ForestTailStage.FirstRefinementReady (List.length_pos_iff.mpr ht.nonempty)
        refinementBudget (e.toFunctionEmbedding :: remaining) S →
        ∃ T : ForestTailStage A B D family t targetTrain allowed,
          ForestTailStage.FirstRefinementReady (List.length_pos_iff.mpr ht.nonempty)
            refinementBudget remaining T ∧ PictureStep S T e.toFunctionEmbedding κ) :
    ∃ T : ForestTailStage A B D family t targetTrain allowed,
      DesignatedArrow T κ := by
  letI : Nonempty family := by
    obtain ⟨b, hb⟩ := baseFamily_nonempty_of_arrow A B D family κ hBase
    exact ⟨⟨b, hb⟩⟩
  let ready : List (UA ↪ P) →
      ForestTailStage A B D family t targetTrain allowed → Prop :=
    ForestTailStage.FirstRefinementReady (List.length_pos_iff.mpr ht.nonempty)
      refinementBudget
  have hTail := initialTail_of_targetCuts A hA B D family t ht targetTrain
    hSupportNonempty hGirth hTargetCuts
  have hReady : ready (projectionProfileList UA P)
      (initialForestTailStage_of_tail A hA B D family t ht targetTrain allowed
        hSupportNonempty hSupportCovers hGirth hTargetParameters hTail) :=
    initialForestTailStage_firstRefinementReady A hA B D family t ht
      targetTrain allowed hSupportNonempty hSupportCovers hGirth
      hTargetParameters hTail refinementBudget (projectionProfileList UA P)
  obtain ⟨T, _, hArrow⟩ := constructFromInitial_of_actualSteps A hA B D family
    t ht targetTrain allowed hSupportNonempty hSupportCovers hGirth
    hTargetParameters hTail κ hBase ready hReady
    (fun _ _ _ h _ => ForestTailStage.FirstRefinementReady.tail h)
    actualStep
  exact ⟨T, hArrow⟩

end StructuralRamsey.Girth.TrainRecursiveWitness

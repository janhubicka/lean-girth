import Girth.TrainRecursiveHJRelationalDesignatedArrow
import Girth.TrainRecursiveNontrivialFibre
import Girth.TrainRecursivePartiteBaseInitial

set_option autoImplicit false
set_option Elab.async false

/-!
# The genuine selected lower forest Ramsey pass needs only geometric local steps

The verified selected finite-pass constructor expects:
  * a relational designated-family Ramsey arrow over the large base;
  * a separate adjacent-parameter proof for each prescribed base copy;
  * the actual target girth and positive labelled-cut bounds;
  * local refining picture steps only for nontrivial physical fibres.

For a finite ordered A-partite target and a part-preserving prescribed
family of embeddings into a larger A-partite base, the first two
items follow from just ONE complete target AdjacentParameters proof
and the genuine partite FAMILY arrow. The base-arrow upgrade uses
ordered-A rigidity and preserves the literal prescribed family label.

This is a conditional FINITE PASS: the remaining input is exactly the
nontrivial-fibre local geometry, including preservation of readiness
and all attached output cycle conditions. It does not postulate a
ready selected output or invoke the full recursive Ramsey theorem.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- A genuine partite-family Ramsey arrow and ONE target-train
parameter bound suffice for the whole selected relational finite
pass, provided the actual refining local steps exist for
nontrivial fibres. This preserves the exact target train and
the original prescribed family labels. -/
theorem constructFromPartiteTargetCuts_of_nontrivialRefiningSteps
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
    (Target : StructuralRamsey.Partite.System L.withOrder UA VB)
    [Finite VB]
    (Large : StructuralRamsey.Partite.System L.withOrder UA P)
    [Finite P]
    (family : Set (Embedding Target.toRelStructure Large.toRelStructure))
    (hSource : Target.IsPartiteOver A₀.ordered)
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
      Large.part (b x) = Target.part x)
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered Target.toRelStructure) t.length)
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (hSupportNonempty :
      Nonempty (OldACarrierEdge A₀.ordered Target.toRelStructure))
    (hSupportCovers : ∀ b : VB,
      ∃ edge : OldACarrierEdge A₀.ordered Target.toRelStructure,
        b ∈ edge.1)
    (hGirth : GirthGT (supportCopies A₀.ordered Target.toRelStructure)
      (t.headD 0))
    (hTargetParameters : targetTrain.AdjacentParameters
      (fun edge => edge.1)
      (fun ν => Target.part ⁻¹' fineAllowed ν))
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        (t.get j))
    (refinementBudget : ℕ)
    (κ : Type w) [Nonempty κ]
    (hPartiteFamily :
      ∀ χ : StructuralRamsey.Partite.Embedding
          (StructuralRamsey.Partite.transversal A₀.ordered) Large → κ,
        ∃ b : StructuralRamsey.Partite.Embedding Target Large,
          b.toEmbedding ∈ family ∧
          ∀ a₁ a₂ : StructuralRamsey.Partite.Embedding
            (StructuralRamsey.Partite.transversal A₀.ordered) Target,
              χ (b.comp a₁) = χ (b.comp a₂))
    (actualStep : ∀ (e : Embedding A₀.ordered Large.toRelStructure)
      (remaining : List (UA ↪ P))
      (S : ForestTailStage A₀.ordered Target.toRelStructure
        Large.toRelStructure family t targetTrain
        (fun ν => Large.part ⁻¹' fineAllowed ν)),
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
        A₀.ordered S.system e.toFunctionEmbedding,
        copyCarrier a.val ≠ copyCarrier b.val) →
      ForestTailStage.FirstRefinementReady
        (List.length_pos_iff.mpr ht.nonempty)
        refinementBudget (e.toFunctionEmbedding :: remaining) S →
      ∃ T : ForestTailStage A₀.ordered Target.toRelStructure
        Large.toRelStructure family t targetTrain
        (fun ν => Large.part ⁻¹' fineAllowed ν),
        ForestTailStage.FirstRefinementReady
          (List.length_pos_iff.mpr ht.nonempty)
          refinementBudget remaining T ∧
        PictureStep S T e.toFunctionEmbedding κ) :
    ∃ T : ForestTailStage A₀.ordered Target.toRelStructure
      Large.toRelStructure family t targetTrain
      (fun ν => Large.part ⁻¹' fineAllowed ν),
      DesignatedArrow T κ := by
  have hParameters := targetParameters_of_partiteFamily_preimage
    A₀.ordered Target Large family hFamilyParts
    targetTrain fineAllowed hTargetParameters
  have hRelationalBase :=
    relationalDesignatedArrow_of_partiteFamily_for_orderedA
      A₀ Target Large family hSource κ hPartiteFamily
  exact constructFromTargetCuts_of_nontrivialRefiningSteps
    A₀ Target.toRelStructure Large.toRelStructure family t ht
    targetTrain (fun ν => Large.part ⁻¹' fineAllowed ν)
    hSupportNonempty hSupportCovers hGirth hParameters hTargetCuts
    refinementBudget κ hRelationalBase actualStep

end StructuralRamsey.Girth.TrainRecursiveWitness

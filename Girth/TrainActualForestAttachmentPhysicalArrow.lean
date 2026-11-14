import Girth.TrainActualForestAttachmentOrderStep
import Girth.TrainPhysicalEdgeToEmbeddingArrow

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual forest picture step: the F_t PHYSICAL-edge Ramsey arrow

The conditional finite attachment theorem previously accepted a
Ramsey arrow on all A-embeddings. The manuscript's F_t axiom
instead colours physical A-support edges. Under unique-image
rigidity of the ambient A-copy, the old physical edge labels
are exactly the finite-picture colouring coordinates.

Use the bridge to convert the physical F_t arrow to the already
checked embedding-arrow interface, then reuse the entire actual
selected train OrderStage/PictureStep construction. No stronger
Ramsey hypothesis and no new gluing or source-copy axiom is added.
The ordered finite case discharges the carrier-rigidity condition
by ordered_embedding_eq_of_sameCopy.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness
open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (RelStructure.Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

section ActualPhysicalEdgeArrow

variable (stage : ForestTailStage A B D family (q :: tail) targetTrain allowed)
variable (hA : A.Irreducible) [Finite UA] [Nontrivial UA]
variable (hBaseLinear : ALinear A D) (e : Embedding A D)
variable (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L P Y) [Finite Y] [Finite I]
variable (f : I → StructuralRamsey.Partite.Embedding
  (stage.system.induce (activeCarrier A stage.system e.toFunctionEmbedding)) E)
variable (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) (q :: tail).length)
variable (bounds : ActiveAttachmentBounds stage hA e active E f U)

local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "RF" => (fun i : I => (f i).toEmbedding)
local notation "OldBottom" => selectedPictureOrderOneData
  A B D stage.system family stage.selected stage.train
  (⟨0, by simp⟩ : Fin ((q :: tail).length + 1))

/-- The next ORDER-stage picture step requires ONLY a physical
A-edge-colouring arrow in the local forest witness. The carrier
rigidity premise is explicit and follows from ordered A in the
intended circulation. All Ramsey selections are the original
selected train family; all actual edge/wagon labels are retained. -/
theorem ForestTailStage.activeAttachment_orderPictureStep_of_finiteMixed_physicalArrow
    (hOldBottom : (OldBottom).FullSystemGirthGT q)
    (hAllBaseStrong : ∀ b : Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (a b : Embedding A (stage.system.toRelStructure.induce S))
    (hTwoSource : ¬ SameCopy a b)
    (hSelectedImages : Function.Injective
      (fun i : I => copyCarrier (RF i)))
    (hLocalMixed : FiniteMixedForestThrough
      (RelationalMixedSupportTest A RF) q)
    (κ : Type w) [Nonempty κ]
    (hCarrierRigid :
      ∀ c d : Embedding A E.toRelStructure, SameCopy c d → c = d)
    (hPhysicalArrow :
      ∀ χ : OldACarrierEdge A E.toRelStructure → κ,
        ∃ i : I,
          ∀ c d : Embedding A (stage.system.induce S).toRelStructure,
            χ (actualEdge ((RF i).comp c)) =
              χ (actualEdge ((RF i).comp d))) :
    ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
      PictureStep stage R.toForestTailStage e.toFunctionEmbedding κ := by
  have hEmbeddingArrow :
      ∀ χ : Embedding A E.toRelStructure → κ,
        ∃ i : I,
          ∀ c d : Embedding A (stage.system.induce S).toRelStructure,
            χ ((RF i).comp c) = χ ((RF i).comp d) :=
    embeddingArrow_of_physicalEdgeArrow RF hCarrierRigid hPhysicalArrow
  exact stage.activeAttachment_orderPictureStep_of_finiteMixed
    hA hBaseLinear e hRigid active E f U bounds
    hOldBottom hAllBaseStrong a b hTwoSource
    hSelectedImages hLocalMixed κ hEmbeddingArrow

end ActualPhysicalEdgeArrow
end StructuralRamsey.Girth.TrainRecursiveWitness

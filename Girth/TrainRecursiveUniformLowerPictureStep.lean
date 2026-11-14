import Girth.TrainRecursiveUniformLowerHJBridge
import Girth.TrainRecursiveActualLowerRefiningStep

set_option autoImplicit false
set_option Elab.async false

/-!
# The nontrivial q>2 picture step from the STRICT lower-rank assertion

The previous conditional picture-step theorem still took a particular
selected lower ForestTailStage, a chosen large HJ base, part-preserving
prescribed copies, and the actual first-wagon refinement as arguments.

This theorem removes ALL those chosen data. The input from induction is
the UNIFORM selected partite forest assertion at every lower vector
  replicate d (q-1) ++ tail, d>0.
Readiness yields the actual refinement at the processed profile;
nontriviality supplies an actual projected source copy; the true active
HJ bridge yields a sufficiently large base and a lower selected stage
with its indexed DesignatedArrow. The local geometry theorem then gives
an actual PictureStep, retaining the complete physical train and every
original positive tail cutoff.

It makes no current-rank induction assumption and does not assume output
supremeness. It does NOT prove the uniform lower assertions, the base
[2]/cutoff-two cases, or the final outer finite pass.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The genuine nontrivial q>2 transition, built from the strictly
smaller-rank UNIVERSAL selected forest hypothesis instead of a freely
supplied lower witness or local-step operator. -/
theorem ForestTailStage.refiningPictureStep_of_uniformLowerRank
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (D : RelStructure L.withOrder P) [Finite P]
    {family : Set (Embedding B D)}
    {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (old : ForestTailStage A₀.ordered B D family (q :: tail)
      targetTrain allowed)
    (ht : Admissible (q :: tail)) (hq : 2 < q)
    (e : Embedding A₀.ordered D)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered old.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val)
    (hBaseLinear : ALinear A₀.ordered D)
    (hStrong : ∀ b : Embedding B D, b ∈ family →
      AStrong A₀.ordered D (copyCarrier b))
    (hTargetTwo : ∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b)
    (κ : Type w) [Fintype κ] [Nonempty κ]
    (hAllLower : ∀ d : ℕ, 0 < d →
      UniformSelectedPartiteForest A₀
        (List.replicate d (q - 1) ++ tail) κ)
    (remaining : List (UA ↪ P))
    (hFresh : e.toFunctionEmbedding ∉ remaining)
    (hReady : ForestTailStage.FirstRefinementReady
      (by simp : 0 < (q :: tail).length) (q - 1)
      (e.toFunctionEmbedding :: remaining) old) :
    ∃ next : ForestTailStage A₀.ordered B D family (q :: tail)
        targetTrain allowed,
      ForestTailStage.FirstRefinementReady
        (by simp : 0 < (q :: tail).length) (q - 1)
        remaining next ∧
      PictureStep old next e.toFunctionEmbedding κ := by
  classical
  have hR := old.firstRefinement_of_ready_head
    (by simp : 0 < (q :: tail).length)
    (q - 1) e.toFunctionEmbedding remaining hReady
  let R := Classical.choice hR
  let active : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered old.system e.toFunctionEmbedding :=
    Classical.choose hPair
  let Source := actualActiveSubsystemPartite A₀.ordered old.system
    e.toFunctionEmbedding
  letI : Finite old.Vertex := old.finiteVertex
  have hLowerAtR : UniformSelectedPartiteForest A₀
      (List.replicate (R.extraCuts + 1) (q - 1) ++ tail) κ :=
    hAllLower (R.extraCuts + 1) (Nat.succ_pos R.extraCuts)
  obtain ⟨N, _hN, hLargePartite, lowerFamily,
    hParts, _hLowerStrong, lower, hLowerArrow⟩ :=
    ForestTailStage.exists_realSelectedLower_of_uniformRank
      A₀ B D old e active ht hq R κ hLowerAtR
  let Large := StructuralRamsey.Partite.Induced.power Source N
  exact ForestTailStage.refiningPictureStep_of_actualLowerSelectedStage
    A₀ B D old ht hq e hPair R Large lower
    hBaseLinear hStrong hTargetTwo hLargePartite hParts
    κ hLowerArrow remaining hFresh hReady

end StructuralRamsey.Girth.TrainRecursiveWitness

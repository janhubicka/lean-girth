import Girth.TrainRecursiveIntrinsicTailSupreme
import Girth.TrainRecursiveActualPairedTailInputs

set_option autoImplicit false
set_option Elab.async false

/-!
# Real lower selected witness implies all original attached positive bounds

The selected lower stage at the TRUE active source and exact first-wagon
refinement supplies its two formerly separate Path A inputs:
- the original shared-source train relation at ALL retained cuts;
- FullSystemGirthGT at EACH original positive threshold t[j].

Consequently, under the intrinsic old-stage geometry of the checked
one-level output theorem, the actual attached selected picture carries
SupremeCycleBound t[j] at every original positive cut.

The coarsened core is the literal selected lower partite stage. Its
selected-copy index subtype, physical A-edges, gluing embeddings and
forgotten train remain unchanged. Neither hRel nor hWitness nor any
attached-output girth is assumed. The genuine lower selected Ramsey
stage itself remains a hypothesis; this does not construct it or the
complete nontrivial PictureStep.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P V : Type v}

/-- Every original positive attached-output SupremeCycleBound is obtained
from one actual refined lower ForestTailStage and intrinsic old geometry,
without separately supplying old/coarse train reflection or gluing
full-system girth. -/
theorem ForestTailStage.attachedAllPositiveSupreme_of_realRefinedLower
    (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA]
    (B : RelStructure L VB) (D : RelStructure L P)
    {family : Set (Embedding B D)}
    {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (old : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (e : Embedding A D)
    (active : StructuralRamsey.Partite.ProjectedEmbedding
      A old.system e.toFunctionEmbedding)
    (Large : StructuralRamsey.Partite.System L UA V)
    (R : FirstWagonRefinement
      (old.train.restrict (sharedOldACarrierInclusion A
        old.system.toRelStructure
        (activeCarrier A old.system e.toFunctionEmbedding)))
      (by simp : 0 < (q :: tail).length)
      (fun edge : SharedOldACarrierEdge A old.system.toRelStructure
        (activeCarrier A old.system e.toFunctionEmbedding) => edge.1.1)
      old.system.part (allowed ⟨1, by simp⟩) (q - 1))
    {lowerFamily : Set (Embedding
      (old.system.toRelStructure.induce
        (activeCarrier A old.system e.toFunctionEmbedding))
      Large.toRelStructure)}
    {lowerAllowed : Fin
      ((List.replicate (R.extraCuts + 1) (q - 1) ++ tail).length + 1) → Set V}
    (lower : ForestTailStage A
      (old.system.toRelStructure.induce
        (activeCarrier A old.system e.toFunctionEmbedding))
      Large.toRelStructure lowerFamily
      (List.replicate (R.extraCuts + 1) (q - 1) ++ tail)
      ((R.train.restrict (inducedACarrierToShared A
        old.system.toRelStructure
        (activeCarrier A old.system e.toFunctionEmbedding))).castHeight
        (actualReplicatedCutoff_height_eq q R.extraCuts tail).symm)
      lowerAllowed)
    (hFamilyParts : ∀ b, b ∈ lowerFamily →
      ∀ x : activeCarrier A old.system e.toFunctionEmbedding,
        Large.part (b x) =
          activeSourcePart A old.system e.toFunctionEmbedding x)
    (hTwoCut : ∀ j : Fin (q :: tail).length, 0 < j.val →
      2 ≤ (q :: tail).get j)
    (hStrong : ∀ r : Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
    (hBaseLinear : ALinear A D)
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e) :
    let E := lower.system.coarsenVia Large lower.isPartite
    let I := {b : DesignatedCopy
      (old.system.toRelStructure.induce
        (activeCarrier A old.system e.toFunctionEmbedding))
      Large.toRelStructure lower.system lowerFamily //
        b ∈ lower.selected}
    let f : I → Embedding
      (old.system.toRelStructure.induce
        (activeCarrier A old.system e.toFunctionEmbedding))
      E.toRelStructure :=
      fun i => (selectedPartiteGluingFamily_of_largeBase
        (actualActiveSubsystemPartite A old.system e.toFunctionEmbedding)
        Large lower.system lower.isPartite lowerFamily hFamilyParts
        lower.selected i).toEmbedding
    let U := (lower.train.castHeight
      (actualReplicatedCutoff_height_eq q R.extraCuts tail)).forgetFirstCuts
      (by simp : 0 < (q :: tail).length)
    ∀ j : Fin (q :: tail).length, 0 < j.val →
      (attachedSelectedPictureOrderOneData
        A hA B D old.system family old.selected e
        E.toRelStructure f old.train U
        (activeCarrier_all_standard_copies_meet_core A
          old.system e.toFunctionEmbedding active I)
        j.castSucc).SupremeCycleBound ((q :: tail).get j) := by
  classical
  let E := lower.system.coarsenVia Large lower.isPartite
  let I := {b : DesignatedCopy
    (old.system.toRelStructure.induce
      (activeCarrier A old.system e.toFunctionEmbedding))
    Large.toRelStructure lower.system lowerFamily // b ∈ lower.selected}
  let f : I → Embedding
    (old.system.toRelStructure.induce
      (activeCarrier A old.system e.toFunctionEmbedding))
    E.toRelStructure :=
      fun i => (selectedPartiteGluingFamily_of_largeBase
        (actualActiveSubsystemPartite A old.system e.toFunctionEmbedding)
        Large lower.system lower.isPartite lowerFamily hFamilyParts
        lower.selected i).toEmbedding
  let U := (lower.train.castHeight
    (actualReplicatedCutoff_height_eq q R.extraCuts tail)).forgetFirstCuts
    (by simp : 0 < (q :: tail).length)
  have hPaired :=
    lower.coarsenedSelected_originalTailAndTrain_of_realRefinedStage
      A old.system e.toFunctionEmbedding Large old.train R hFamilyParts
  dsimp only
  exact ForestTailStage.attachedAllPositiveSupreme_of_intrinsicWitness
    A hA B D old e E.toRelStructure f U active
    hPaired.1 hTwoCut hStrong hTargetTwo hBaseLinear hRigid hPaired.2

end StructuralRamsey.Girth.TrainRecursiveWitness

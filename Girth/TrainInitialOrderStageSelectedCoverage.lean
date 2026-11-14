import Girth.TrainInitialOrderStageFromTargetCuts
import Girth.TrainActualSelectedBaseCoverage

set_option autoImplicit false
set_option Elab.async false

/-!
# The genuine initial OrderStage covers EVERY prescribed base B-copy

The initial selected picture is the disjoint union of one literal B
copy for every member of the prescribed family. The checked
initialPicture_lifts theorem witnesses selected base coverage.

Together with the checked initial system-girth theorem, this gives
a true initial CoveredBottomReady stage for the finite pass:
bottom full system girth at q PLUS retained selected lifts of all
base copies. No independently assumed all-base strongness.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The same input assumptions as initialOrderStage_of_allTargetCuts
give an initial OrderStage WITH a proof that every prescribed base
B-embedding has a selected lift. Neither the initial girth bound
nor selected-base coverage is taken as an extra oracle. -/
noncomputable def initialCoveredOrderStage_of_allTargetCuts
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) [Finite VB]
    (D : RelStructure L P) [Finite P]
    (family : Set (RelStructure.Embedding B D)) [Nonempty family]
    (q : ℕ) (tail : List ℕ)
    (ht : Admissible (q :: tail))
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length)
    (allowed : Fin ((q :: tail).length + 1) → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ b : VB,
      ∃ e : OldACarrierEdge A B, b ∈ e.1)
    (hTargetParameters : ∀ b : family,
      targetTrain.AdjacentParameters (fun edge => edge.1)
        (fun ν => b.1 ⁻¹' allowed ν))
    (hCutoff : ∀ j : Fin (q :: tail).length,
      2 ≤ (q :: tail).get j)
    (hTargetCut : ∀ j : Fin (q :: tail).length,
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        ((q :: tail).get j)) :
    {S : OrderStage A B D family (q :: tail) targetTrain allowed //
      S.toForestTailStage.CoversBase} := by
  let S := initialOrderStage_of_allTargetCuts
    A hA B D family q tail ht targetTrain allowed
    hSupportNonempty hSupportCovers hTargetParameters hCutoff hTargetCut
  refine ⟨S, ?_⟩
  intro b hb
  change ∃ q : DesignatedCopy B D
      (StructuralRamsey.Partite.Initial.picture B
        (fun b : family => b.1.toFunctionEmbedding)) family,
      q ∈ initialSelected B D family ∧ q.base = b
  exact initialPicture_lifts B D family b hb

/-- No additional initial readiness is needed for the finite pass:
the disjoint initial source already carries bottom girth at q and
selected base coverage, and these remain the same physical data
when the OrderStage is viewed as a ForestTailStage. -/
theorem initialCoveredOrderStage_bottomReady
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) [Finite VB]
    (D : RelStructure L P) [Finite P]
    (family : Set (RelStructure.Embedding B D)) [Nonempty family]
    (q : ℕ) (tail : List ℕ)
    (ht : Admissible (q :: tail))
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length)
    (allowed : Fin ((q :: tail).length + 1) → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ b : VB,
      ∃ e : OldACarrierEdge A B, b ∈ e.1)
    (hTargetParameters : ∀ b : family,
      targetTrain.AdjacentParameters (fun edge => edge.1)
        (fun ν => b.1 ⁻¹' allowed ν))
    (hCutoff : ∀ j : Fin (q :: tail).length,
      2 ≤ (q :: tail).get j)
    (hTargetCut : ∀ j : Fin (q :: tail).length,
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        ((q :: tail).get j)) :
    let S := initialCoveredOrderStage_of_allTargetCuts
      A hA B D family q tail ht targetTrain allowed
      hSupportNonempty hSupportCovers hTargetParameters hCutoff hTargetCut
    S.1.toForestTailStage.CoversBase := by
  exact (initialCoveredOrderStage_of_allTargetCuts
    A hA B D family q tail ht targetTrain allowed
    hSupportNonempty hSupportCovers hTargetParameters hCutoff hTargetCut).2

end StructuralRamsey.Girth.TrainRecursiveWitness

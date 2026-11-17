import Girth.TrainCoverageFreeOrderPass
import Girth.TrainCoverageFreeComparison
import Girth.TrainInitialOrderStageSelectedCoverage

set_option autoImplicit false
set_option Elab.async false

/-!
# The actual initial disjoint picture starts the COVERAGE-FREE pass

The initial disjoint picture is already kernel-checked in the stronger
ForestTailStage formalism (conditional on the real target's labelled
wagon girth, A-support coverage and parameters). The standalone F_t
to R_t conversion uses exactly the same physical initial train,
selected original B-copies, part structure and old cut bounds, but
does not need mixed irreducible coverage.

The checked initialCoveredOrderStage_of_allTargetCuts returns a real
OrderStage and literal selected lift of every prescribed base B-copy.
The forgetful CoverageFree.OrderStage.ofStrong loses only the
unneeded mixedCoverage proof. It therefore satisfies CoverageFree.Ready:
bottom system girth at the SAME q and selected base coverage.
Nothing is reconstructed, no new initial girth theorem is postulated.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v

/-- The original initial train picture has a coverage-free OrderStage
and the exact two finite-pass readiness fields, derived from the
target's labelled wagon girth at its own cutoff vector. This supplies
an actual initial object for the standalone F_t => R_t construction,
not an axiom or an extra mixed-cover assumption. -/
noncomputable def initialOrderStageReady_of_targetCuts
    {L : RelLanguage.{u}} {UA VB P : Type v}
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) [Finite VB]
    (D : RelStructure L P) [Finite P]
    (family : Set (Embedding B D)) [Nonempty family]
    (q : ℕ) (tail : List ℕ)
    (ht : Admissible (q :: tail))
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A B) (q :: tail).length)
    (allowed : Fin ((q :: tail).length + 1) → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ b : VB,
      ∃ edge : OldACarrierEdge A B, b ∈ edge.1)
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
      S.toForestStage.Ready} := by
  let old := TrainRecursiveWitness.initialCoveredOrderStage_of_allTargetCuts
    A hA B D family q tail ht targetTrain allowed
    hSupportNonempty hSupportCovers hTargetParameters hCutoff hTargetCut
  let S := OrderStage.ofStrong old.1
  have hBottom :
      (selectedPictureOrderOneData
        A B D S.system family S.selected S.train
        (⟨0, by simp⟩ : Fin ((q :: tail).length + 1))).FullSystemGirthGT q := by
    simpa only [S, OrderStage.ofStrong, ForestStage.ofStrong] using
      old.1.allCutGirth
        (⟨0, by simp⟩ : Fin (q :: tail).length)
  have hBase : S.toForestStage.CoversBase := by
    intro b hb
    exact old.2 b hb
  exact ⟨S, hBottom, hBase⟩

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

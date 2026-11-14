import Girth.TrainForestStageTrueActiveSameVectorGirth
import Girth.TrainForestStageCoveredNontrivialPass
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Final conditional same-vector finite F_t -> R_t pass

The finite Ramsey pass needs an actual local operator ONLY on a
physical A-profile with two different A-copy image carriers. Its
old stage already has bottom full system girth q and every positive
proper system cut at its own t_j. Passing to the true induced active
train preserves the FULL LABELLED WAGON GIRTH vector, without
claiming its nonhereditary full system-girth property.

This module packages that exact active-train input as one named
predicate and uses the checked nontrivial-fibre dispatch to run the
entire finite selected Ramsey pass, skipping subsingleton fibres
by identity, keeping CoversBase and bottom full system girth.

The ONLY remaining LOCAL assumption is an honest F_t operator:
for every actual nontrivial active fibre with labelled girth at
the same vector, supply a selected local ORDER picture step. The
new companion module TrainActualFtNontrivialLocalStep shows how
the concrete F_t partite witness, finite mixed forest, exact
positive bounds, physical edge-colouring arrow, selected image
distinctness and train reflection construct that local step.

This theorem does not assert that an arbitrary ordered B-target
has such a local F_t witness. That existence is the exact
Ramsey-input/girth-preserving construction task still open.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered

variable {B : RelStructure L.withOrder VB}
variable {D : RelStructure L.withOrder P}
variable {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

/-- Exactly the SAME-vector labelled wagon-girth premise needed
to apply F_t to the honest active induced train. The double
restriction is by actual support-edge labels with injective wagon
quotient maps, not by replacing the full selected picture. -/
def ForestTailStage.ActiveWagonGirth
    (S : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (e : Embedding A D) : Prop :=
  ∀ j : Fin (q :: tail).length,
    LabelledGirthGT
      ((((S.train.restrict
        (sharedOldACarrierInclusion A S.system.toRelStructure
          (activeCarrier A S.system e.toFunctionEmbedding))).restrict
        (inducedACarrierToShared A S.system.toRelStructure
          (activeCarrier A S.system e.toFunctionEmbedding))).wagonClassCarrier
        (fun edge : OldACarrierEdge A
          (S.system.toRelStructure.induce
            (activeCarrier A S.system e.toFunctionEmbedding)) => edge.1)
        j.castSucc))
      ((q :: tail).get j)

/-- The old BottomReady and tail bounds already supply the
LOCAL F_t INPUT girth at the SAME vector for every actual base
profile; no independent active-subsystem girth assumption. -/
theorem ForestTailStage.activeWagonGirth_of_bottomReady
    (S : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (hReady : S.BottomReady) (e : Embedding A D) :
    S.ActiveWagonGirth A₀ e := by
  exact S.trueActive_inducedSameVectorCutGirth e hReady

/-- Entire finite selected strong-train ORDER Ramsey pass from a
genuine local F_t step available on nontrivial active fibres whose
inherited wagon cut girths are the original q :: tail values.
The one-edge/subsingleton fibres are skipped by the checked
identity transition; selected coverage and bottom girth remain
true throughout without an extra readiness-drop theorem. -/
theorem ForestTailStage.ramseyOrderPass_of_Ft_eligible_steps
    (S : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) [Nonempty κ]
    (hInitial : S.CoveredBottomReady)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (hBase : ∀ χ : Embedding A D → κ,
      ∃ b : Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (localFt : ∀ (e : Embedding A D) (remaining : List (UA ↪ P))
      (T : ForestTailStage A B D family (q :: tail) targetTrain allowed),
      T.CoveredBottomReady →
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A T.system
        e.toFunctionEmbedding,
        copyCarrier a.val ≠ copyCarrier b.val) →
      T.ActiveWagonGirth A₀ e →
      ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
        PictureStep T R.toForestTailStage e.toFunctionEmbedding κ) :
    ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
      ∀ χ : Embedding A R.system.toRelStructure → κ,
        ∃ b : DesignatedCopy B D R.system family,
          b ∈ R.selected ∧
          AStrong A R.system.toRelStructure (copyCarrier b.embedding) ∧
          (∀ μ : Fin ((q :: tail).length + 1),
            ∀ a₁ a₂ : Embedding A B,
              R.train.rel μ
                (actualEdge (b.embedding.comp a₁))
                (actualEdge (b.embedding.comp a₂)) ↔
              targetTrain.rel μ (actualEdge a₁) (actualEdge a₂)) ∧
          (∀ a₁ a₂ : Embedding A B,
            χ (b.embedding.comp a₁) = χ (b.embedding.comp a₂)) := by
  apply S.ramseyOrderPass_of_nontrivial_order_steps
    A₀ profiles κ hInitial hProfiles hBase
  intro e remaining T hReady hPair
  exact localFt e remaining T hReady hPair
    (T.activeWagonGirth_of_bottomReady A₀ hReady.1 e)

end StructuralRamsey.Girth.TrainRecursiveWitness

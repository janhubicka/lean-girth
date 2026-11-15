import Girth.TrainCoverageFreeTrueActiveGirth
import Girth.TrainCoverageFreeStrongFinitePass

set_option autoImplicit false
set_option Elab.async false

/-!
# The standalone F_t -> R_t finite pass: exact F_t input girth

At every nontrivial physical A-fibre, the actual selected old
coverage-free ForestStage has bottom FullSystemGirthGT q and
positive FullSystemGirthGT at every retained coordinate. The
checked full-system-to-labelled-girth converse plus the two
literal physical restrictions give labelled wagon girth on the
TRUE induced active source at the SAME vector q::tail.

The standalone F_t witness only requires that labelled wagon-girth
premise: it does NOT require mixed irreducible coverage, active
full-system girth, a modified train, extra colours or a stronger
embedding-colouring Ramsey arrow.

This module packages the existing coverage-free finite-pass
combinatorics with that exact inherited-girth input. The sole
external per-fibre operator must choose a genuine finite local
F_t partite train witness and construct a selected coverage-free
OrderStage/PictureStep. Subsinge physical fibres use identity.
The resulting Ramsey copy is an ORIGINAL selected strong B-train
copy with all target train relations reflected.

This is deliberately a CONDITIONAL theorem, not a declaration
of the unformalized abstract assertion F_t or its existence.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

variable (A₀ : RelStructure L UA)
variable [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered

variable {B : RelStructure L.withOrder VB}
variable {D : RelStructure L.withOrder P}
variable {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels
  (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

/-- Exact labelled wagon girth of the honest active source at
all entries of the SAME q::tail vector, with the complete
original physical edge labels and their restricted wagon relation. -/
def ForestStage.ActiveWagonGirth
    (S : ForestStage A B D family (q :: tail) targetTrain allowed)
    (e : Embedding A D) : Prop :=
  ∀ j : Fin (q :: tail).length,
    LabelledGirthGT
      (((S.train.restrict
        (sharedOldACarrierInclusion A S.system.toRelStructure
          (activeCarrier A S.system e.toFunctionEmbedding))).restrict
        (inducedACarrierToShared A S.system.toRelStructure
          (activeCarrier A S.system e.toFunctionEmbedding))).wagonClassCarrier
          (fun edge : OldACarrierEdge A
            (S.system.toRelStructure.induce
              (activeCarrier A S.system e.toFunctionEmbedding)) =>
                edge.1)
          j.castSucc)
      ((q :: tail).get j)

/-- Readiness of the original picture provides the exact
local F_t active wagon-girth requirement, not a stronger
active system-girth requirement. -/
theorem ForestStage.activeWagonGirth_of_ready
    (S : ForestStage A B D family (q :: tail) targetTrain allowed)
    (hReady : S.Ready)
    (e : Embedding A D) :
    S.ActiveWagonGirth A₀ e :=
  S.trueActive_sameVectorCutGirth e hReady.1

/-- Complete selected strong-train finite Ramsey pass under ONE
genuine local F_t choice on each nontrivial physical profile
with the inherited same-vector wagon girth. Identity steps
cover all subsingleton profiles. The local F_t choice remains
a concrete existence obligation, not a new theorem oracle. -/
theorem ForestStage.ramseyStrongTrain_of_Ft_eligible_steps
    (S : ForestStage A B D family (q :: tail) targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) [Nonempty κ]
    (hInitial : S.Ready)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (hBaseArrow : ∀ χ : Embedding A D → κ,
      ∃ b : Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (localFt : ∀ (e : Embedding A D)
      (remaining : List (UA ↪ P))
      (T : ForestStage A B D family (q :: tail) targetTrain allowed),
      T.Ready →
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
        A T.system e.toFunctionEmbedding,
        copyCarrier a.val ≠ copyCarrier b.val) →
      T.ActiveWagonGirth A₀ e →
      ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
        PictureStep T R.toForestStage
          e.toFunctionEmbedding κ) :
    ∃ R : OrderStage A B D family
        (q :: tail) targetTrain allowed,
      ∀ χ : Embedding A R.system.toRelStructure → κ,
        ∃ b : DesignatedCopy B D R.system family,
          b ∈ R.selected ∧
          AStrong A R.system.toRelStructure
            (copyCarrier b.embedding) ∧
          (∀ μ : Fin ((q :: tail).length + 1),
            ∀ a₁ a₂ : Embedding A B,
              R.train.rel μ
                (actualEdge (b.embedding.comp a₁))
                (actualEdge (b.embedding.comp a₂)) ↔
              targetTrain.rel μ
                (actualEdge a₁) (actualEdge a₂)) ∧
          (∀ a₁ a₂ : Embedding A B,
            χ (b.embedding.comp a₁) =
              χ (b.embedding.comp a₂)) := by
  apply S.ramseyStrongTrain_of_nontrivialFtSteps
    A₀ profiles κ hInitial hProfiles hBaseArrow
  intro e remaining T hReady hTwo
  exact localFt e remaining T hReady hTwo
    (T.activeWagonGirth_of_ready A₀ hReady e)

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

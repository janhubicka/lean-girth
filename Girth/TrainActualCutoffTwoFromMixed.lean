import Girth.TrainActualWitnessTopTwoFromMixed
import Girth.TrainSelectedPictureStageAssembly

set_option autoImplicit false
set_option Elab.async false

/-!
# Discharge the actual cutoff-two full-system witness requirement

ActiveAttachmentBounds.cutoffTwo previously requested SOME local
witness cut with genuine FullSystemGirthGT >=2 whenever the leading
cutoff is two. This is not a consequence of F_2's bottom forest
property alone: a four-copy mixed cycle gives a counterexample.

The universal top is different. It has a unique physical wagon
parent, so the separate structural top-order-two theorem applies.
The actual SAME-cutoff F_2 mixed finite-set property yields its
A-linearity and strong-copy premises, while the true active source
supplies vertex support coverage. Thus choose μ = universal top
and q = 2. This is the exact existential field of ActiveAttachmentBounds
with no extra witness-girth input or stronger Ramsey assumption.

No reduction of the positive proper cutoffs is made.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I : Type v}

/-- The original F_t mixed forest property at its own leading cutoff
supplies a genuine cutoff-two FULL system-girth witness, choosing
the universal top when that leading cutoff equals two. -/
theorem activeGluingWitness_cutoffTwo_of_sameVectorMixed
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P) (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m : ℕ}
    (U : EdgeTrainLevels (OldACarrierEdge A R) m)
    (cutoff : ℕ)
    (hForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A f) cutoff) :
    cutoff = 2 →
      ∃ μ : Fin (m + 1), ∃ q : ℕ, 2 ≤ q ∧
        (activeGluingWitnessOrderOneData
          A C α R f U μ).FullSystemGirthGT q := by
  intro hTwo
  have hForestTwo :
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A f) 2 := by
    simpa [hTwo] using hForest
  refine ⟨⟨m, Nat.lt_succ_self m⟩, 2, by omega, ?_⟩
  exact activeGluingWitness_top_fullSystemGirth_two_of_finiteMixed
    A C α R f U hForestTwo

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- Exactly the cutoffTwo field in the actual attachment stage
specification. A same-vector F_t local mixed forest supplies it
without assuming an unrelated local full system-girth witness. -/
theorem ActiveAttachmentBounds.cutoffTwo_of_finiteMixed
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (stage.system.induce
        (activeCarrier A stage.system e.toFunctionEmbedding)) E)
    (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) t.length)
    (hMixed : FiniteMixedForestThrough
      (RelationalMixedSupportTest A (fun i => (f i).toEmbedding))
      (t.headD 0)) :
    t.headD 0 = 2 →
      ∃ μ : Fin (t.length + 1), ∃ q : ℕ, 2 ≤ q ∧
        (activeGluingWitnessOrderOneData
          A stage.system e.toFunctionEmbedding E.toRelStructure
          (fun i => (f i).toEmbedding) U μ).FullSystemGirthGT q := by
  exact activeGluingWitness_cutoffTwo_of_sameVectorMixed
    A stage.system e.toFunctionEmbedding E.toRelStructure
    (fun i => (f i).toEmbedding) U (t.headD 0) hMixed

end StructuralRamsey.Girth.TrainRecursiveWitness

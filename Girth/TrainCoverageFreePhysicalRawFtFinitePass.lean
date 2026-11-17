import Girth.TrainCoverageFreePhysicalRawFtWitness
import Girth.TrainCoverageFreePhysicalInitialFinitePass
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Initial-to-final same-vector F_t -> R_t from genuine RAW local forests

The only local existence premise is a typed F_t witness on each
NONTRIVIAL physical projected fibre. Its fineEdges condition is
literal one-edge coloured type, NOT full ordered IsPartiteOver.
The actual physical picture step is constructed from this witness,
with no output girth or already-completed Ramsey step assumed.
Zero/singleton fibres use the identity step.

This is still CONDITIONAL on actual existence of the raw F_t
witness at the same cutoff vector; abstract F_t itself is not
formalized as a quantified Lean principle here. The independent
auxiliary order-compatibility invariant must also be maintained
through the actual attachment and final order-extension.
UNCOMPILED SOURCE, no kernel/axiom validation.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- Full selected strong train Ramsey arrow from the initial
disjoint picture, provided the standalone forest assertion can
construct precisely the raw, no-isolated-vertices local objects
on each nontrivial true active source. -/
theorem initialStrongTrainRamsey_of_rawFtWitnesses
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nontrivial UA] [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (D : RelStructure L.withOrder P) [Finite P]
    (family : Set (Embedding B D)) [Nonempty family]
    (q : ℕ) (tail : List ℕ)
    (ht : Admissible (q :: tail))
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) (q :: tail).length)
    (allowed : Fin ((q :: tail).length + 1) → Set P)
    (hSupportNonempty :
      Nonempty (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ b : VB,
      ∃ edge : OldACarrierEdge A₀.ordered B, b ∈ edge.1)
    (hTargetParameters : ∀ b : family,
      targetTrain.AdjacentParameters (fun edge => edge.1)
        (fun ν => b.1 ⁻¹' allowed ν))
    (hCutoff : ∀ j : Fin (q :: tail).length,
      2 ≤ (q :: tail).get j)
    (hTargetCut : ∀ j : Fin (q :: tail).length,
      LabelledGirthGT
        (targetTrain.wagonClassCarrier
          (fun edge => edge.1) j.castSucc)
        ((q :: tail).get j))
    (hBaseLinear : ALinear A₀.ordered D)
    (hBaseStrong :
      ∀ b : Embedding B D, b ∈ family →
        AStrong A₀.ordered D (copyCarrier b))
    (hTargetTwo :
      ∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b)
    (κ : Type w) [Nonempty κ]
    (hBaseArrow :
      ∀ χ : Embedding A₀.ordered D → κ,
        ∃ b : Embedding B D, b ∈ family ∧
          ∀ a₁ a₂ : Embedding A₀.ordered B,
            χ (b.comp a₁) = χ (b.comp a₂))
    (rawFt :
      ∀ (e : Embedding A₀.ordered D)
        (remaining : List (UA ↪ P))
        (T : PhysicalForestStage A₀.ordered B D family
          (q :: tail) targetTrain allowed),
        T.Ready →
        (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
          A₀.ordered T.system e.toFunctionEmbedding,
          copyCarrier a.val ≠ copyCarrier b.val) →
        T.ActiveWagonGirth A₀ e →
        Nonempty (RawPartiteFtWitness A₀ T e κ)) :
    ∃ R : PhysicalOrderStage A₀.ordered B D family
      (q :: tail) targetTrain allowed,
      ∀ χ : Embedding A₀.ordered R.system.toRelStructure → κ,
        ∃ b : DesignatedCopy B D R.system family,
          b ∈ R.selected ∧
          AStrong A₀.ordered R.system.toRelStructure
            (copyCarrier b.embedding) ∧
          (∀ μ : Fin ((q :: tail).length + 1),
            ∀ a₁ a₂ : Embedding A₀.ordered B,
              R.train.rel μ
                (actualEdge (b.embedding.comp a₁))
                (actualEdge (b.embedding.comp a₂)) ↔
              targetTrain.rel μ
                (actualEdge a₁) (actualEdge a₂)) ∧
          (∀ a₁ a₂ : Embedding A₀.ordered B,
            χ (b.embedding.comp a₁) =
              χ (b.embedding.comp a₂)) := by
  apply initialStrongTrainRamsey_of_nontrivialFtOperator
    A₀ B D family q tail ht targetTrain allowed
    hSupportNonempty hSupportCovers hTargetParameters
    hCutoff hTargetCut κ hBaseArrow
  intro e remaining T hReady hPair hWagonGirth
  let W : RawPartiteFtWitness A₀ T e κ :=
    Classical.choice
      (rawFt e remaining T hReady hPair hWagonGirth)
  have hSelectedStrong :
      ∀ b : DesignatedCopy B D T.system family,
        b ∈ T.selected →
          AStrong A₀.ordered D (copyCarrier b.base) := by
    intro b _hb
    exact hBaseStrong b.base b.base_mem
  exact W.toPictureStep A₀ T e κ
    hBaseLinear hReady hSelectedStrong
    hTargetTwo hCutoff hPair

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

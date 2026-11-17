import Girth.TrainCoverageFreeInitialStage
import Girth.TrainCoverageFreePhysicalFtEligiblePass

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact initial-to-final standalone F_t -> R_t finite picture interface

The initial disjoint picture carries system girth at the SAME
q::tail vector, selected original B copies, every base B lift,
complete physical A-support and literal target train restrictions.
The coverage-free initial object forgets ONLY the unnecessary
recursive mixed irreducible-cover certificate.

The coverage-free finite selected Ramsey pass is already a
structural theorem. Feeding the genuine initial stage to that
pass gives a final selected strong train Ramsey object, under
ONE precisely stated remaining local input: on each nontrivial
physical A-fibre, construct an actual coverage-free PhysicalOrderStage
PictureStep using the same-vector F_t witness.

No independent initial-girth, mixedCoverage, per-profile readiness,
one-edge attachment, arbitrary local FullSystemGirth, or output
system-girth premise is assumed. The real remaining task is
constructing that nontrivial local F_t operator and its exact
fine-part / physical train identification.
-/

/-!
Physical initial-to-final strong-train pass. The original genuine
initial disjoint picture is reused unchanged, then its extra
IsPartiteOver certificate is forgotten to ProjectsACopies.
No artificial initial-girth or selected base-coverage assumptions
are introduced. Nontrivial local F_t choice remains OPEN. Uncompiled.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- A true target train of exact labelled wagon girth q::tail has
an initial coverage-free picture, and the checked finite selected
pass gives a final strong original B-train Ramsey arrow provided
the honest SAME-VECTOR local F_t operator exists on every
nontrivial physical fibre. This is a conditional FINITE-PASS
reduction, not an assertion of the local operator's existence. -/
theorem initialStrongTrainRamsey_of_nontrivialFtOperator
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
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
    (κ : Type w) [Nonempty κ]
    (hBaseArrow :
      ∀ χ : Embedding A₀.ordered D → κ,
        ∃ b : Embedding B D, b ∈ family ∧
          ∀ a₁ a₂ : Embedding A₀.ordered B,
            χ (b.comp a₁) = χ (b.comp a₂))
    (localFt : ∀ (e : Embedding A₀.ordered D)
      (remaining : List (UA ↪ P))
      (T : PhysicalForestStage A₀.ordered B D family
        (q :: tail) targetTrain allowed),
      T.Ready →
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
        A₀.ordered T.system e.toFunctionEmbedding,
        copyCarrier a.val ≠ copyCarrier b.val) →
      T.ActiveWagonGirth A₀ e →
      ∃ O : PhysicalOrderStage A₀.ordered B D family
          (q :: tail) targetTrain allowed,
        PictureStep T O.toPhysicalForestStage
          e.toFunctionEmbedding κ) :
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
  let hA : A₀.ordered.Irreducible :=
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  let old := initialOrderStageReady_of_targetCuts
    A₀.ordered hA
    B D family q tail ht targetTrain allowed
    hSupportNonempty hSupportCovers
    hTargetParameters hCutoff hTargetCut
  let start : PhysicalOrderStage A₀.ordered B D family
      (q :: tail) targetTrain allowed :=
    PhysicalOrderStage.ofStrong hA old.1
  have hInitial : start.toPhysicalForestStage.Ready := by
    constructor
    · simpa only [start, PhysicalOrderStage.ofStrong,
        PhysicalForestStage.ofStrong] using old.2.1
    · intro b hb
      exact old.2.2 b hb
  classical
  letI : Fintype (UA ↪ P) := Fintype.ofFinite (UA ↪ P)
  let profiles : List (UA ↪ P) := Finset.univ.toList
  have hProfiles : ∀ α : UA ↪ P, α ∈ profiles := by
    intro α
    exact Finset.mem_toList.mpr (Finset.mem_univ α)
  exact start.toPhysicalForestStage.ramseyStrongTrain_of_Ft_eligible_steps
    A₀ profiles κ hInitial hProfiles hBaseArrow localFt

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

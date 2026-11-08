import Girth.TrainRecursiveActualCoarsenedFullRecursiveCutoffs
import Girth.TrainRecursiveExactRetainedFullSystemGirth
import Girth.TrainRecursiveExactOriginalRetainedCutoff
import Girth.TrainRecursiveActualFullSystemHeightTransport
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Genuine lower selected tail girth supplies ALL old positive gluing cutoffs

The literal lower request is replicate (r+1) (q-1) ++ tail. Original
positive cut j corresponds to lower fine cut j+r, carrying exactly
the ORIGINAL varying cutoff (q::tail).get j, potentially greater than q.

The actual selected lower ForestTailStage supplies that positive
FullSystemGirthGT. Complete physical-incidence transfer, exact train
height equality, and the verified forgetFirstCuts mapping preserve
that exact certificate at the corresponding original positive cut.

No invented lower stage, extra full-system premise, physical-edge
pruning, selected-label quotient or assumed attached-output girth.
The output SupremeCycleBound and nontrivial PictureStep remain separate.
Circulation only; no appendix or TeX marker changes.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
universe u v

variable {L : RelLanguage.{u}} {UA P V X : Type v}

private theorem actualSelectedOriginalHeightEq (q r : ℕ) (tail : List ℕ) :
    (q :: tail).length + r =
      (List.replicate (r + 1) (q - 1) ++ tail).length := by
  simp only [List.length_cons, List.length_append, List.length_replicate]
  omega

variable (A : RelStructure L UA)
variable (Old : StructuralRamsey.Partite.System L P X)
variable (α : UA ↪ P)
variable (D : StructuralRamsey.Partite.System L UA V)

local notation "Source" =>
  Old.toRelStructure.induce (activeCarrier A Old α)
local notation "Target" =>
  actualActiveSubsystemPartite A Old α

variable {q r : ℕ} {tail : List ℕ}
variable {family : Set (Embedding Source D.toRelStructure)}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A Source)
  (List.replicate (r + 1) (q - 1) ++ tail).length}
variable {allowed :
  Fin ((List.replicate (r + 1) (q - 1) ++ tail).length + 1) → Set V}
variable (S : ForestTailStage A Source D.toRelStructure family
  (List.replicate (r + 1) (q - 1) ++ tail) targetTrain allowed)
variable (hFamilyParts : ∀ b, b ∈ family →
  ∀ x : activeCarrier A Old α,
    D.part (b x) = activeSourcePart A Old α x)

local notation "E" => S.system.coarsenVia D S.isPartite
local notation "Selected" =>
  {b : DesignatedCopy Source D.toRelStructure S.system family //
    b ∈ S.selected}
local notation "Gluing" => fun i : Selected =>
  (selectedPartiteGluingFamily_of_largeBase
    Target D S.system S.isPartite family hFamilyParts
    S.selected i).toEmbedding

include hFamilyParts

/-- Genuine positive lower tail system girth, preserved at the EXACT
original old positive cutoff after literal height casting and forgetting
extra first-wagon cuts. -/
theorem ForestTailStage.coarsenedSelected_originalPositiveFullSystem
    (j : Fin (q :: tail).length) (hj : 0 < j.val) :
    (activeGluingWitnessOrderOneData A Old α E.toRelStructure
      Gluing
      ((S.train.castHeight
        (actualSelectedOriginalHeightEq q r tail).symm).forgetFirstCuts
          (by simp : 0 < (q :: tail).length))
      j.castSucc).FullSystemGirthGT ((q :: tail).get j) := by
  let m := (q :: tail).length
  have hm : 0 < m := by simp [m]
  have hLen : m + r =
      (List.replicate (r + 1) (q - 1) ++ tail).length :=
    actualSelectedOriginalHeightEq q r tail
  let jLower : Fin (List.replicate (r + 1) (q - 1) ++ tail).length :=
    ⟨j.val + r, by
      have hjLt := j.isLt
      simp only [List.length_cons] at hjLt
      simp only [List.length_append, List.length_replicate]
      omega⟩
  have hjLowerPos : 0 < jLower.val := by
    change 0 < j.val + r
    omega
  have hCutoff :
      (List.replicate (r + 1) (q - 1) ++ tail).get jLower =
        (q :: tail).get j := by
    exact originalPositiveCutoff_eq_lowerRetained q r tail j hj
  have hOriginalFull :
      (activeGluingWitnessOrderOneData A Old α E.toRelStructure
        Gluing S.train jLower.castSucc).FullSystemGirthGT
        ((q :: tail).get j) := by
    have h := S.coarsenedSelected_fullSystem_at_positive
      A Old α D hFamilyParts jLower hjLowerPos
    rw [hCutoff] at h
    exact h
  let μ : Fin (m + 1) := j.castSucc
  let ν : Fin (m + r + 1) :=
    EdgeTrainLevels.firstForgetIndex m r μ
  have hLevel :
      Fin.cast (congrArg (fun k : ℕ => k + 1) hLen) ν =
        jLower.castSucc := by
    apply Fin.ext
    change (if j.val = 0 then 0 else j.val + r) = j.val + r
    simp [Nat.ne_of_gt hj]
  have hCast :
      Fin.cast (congrArg (fun k : ℕ => k + 1) hLen.symm).symm ν =
        Fin.cast (congrArg (fun k : ℕ => k + 1) hLen) ν := by
    apply Fin.ext
    rfl
  have hFine :
      (activeGluingWitnessOrderOneData A Old α E.toRelStructure
        Gluing (S.train.castHeight hLen.symm) ν).FullSystemGirthGT
          ((q :: tail).get j) := by
    apply activeGluingWitness_fullSystemGirth_castHeight
      A Old α E.toRelStructure Gluing S.train hLen.symm
      ν ((q :: tail).get j)
    rw [hCast, hLevel]
    exact hOriginalFull
  exact activeGluingWitness_retainedFullSystem_of_fine
    A Old α E.toRelStructure Gluing
    (S.train.castHeight hLen.symm) hm μ ((q :: tail).get j) hFine

end StructuralRamsey.Girth.TrainRecursiveWitness

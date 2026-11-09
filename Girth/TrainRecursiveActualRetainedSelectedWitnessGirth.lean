import Girth.TrainRecursiveActualCoarsenedFullSystem
import Girth.TrainRecursiveActualHeightCutoffApplication
import Girth.TrainRecursiveExactOriginalRetainedCutoff
import Girth.TrainRecursiveExactRetainedFullSystemGirth
import Girth.TrainRecursiveActualFullSystemHeightTransport
import Girth.TrainRecursiveFullRetainedWitnessTransfer
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact original positive shared-witness girth from the ACTUAL lower stage

A genuinely selected lower ForestTailStage over the whole true active
source supplies FullSystemGirthGT at each of its positive fine cuts.
The original old positive cut j has actual fine coordinate j+r in
replicate (r+1) (q-1) ++ tail, where its lower cutoff is EXACTLY
(q::tail).get j. The complete selected physical gluing incidence
is transported across the genuine equality of train heights, then
the first r added cuts are forgotten. This produces the lower SHARED
witness's complete original FullSystemGirthGT at the same t[j],
including global simultaneous supreme plans.

No Hales--Jewett-power girth, deleted ambient A-edge, equality-carrier
index quotient, physical witness existence, or output girth is assumed.
The REAL selected lower stage and its part-preserving family are inputs.
This precisely discharges the positive original hWitness assumption
of the conditional intrinsic output/tail-supreme bridge.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {UA P V X : Type v}

/-- Every original positive retained cutoff is inherited with its exact
FULL physical system-girth threshold by the genuine selected lower
shared witness after equality-of-height transport and cut forgetting. -/
theorem ForestTailStage.coarsenedSelected_retainedSharedFullSystem_of_realStage
    (A : RelStructure L UA)
    (Old : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P)
    (Large : StructuralRamsey.Partite.System L UA V)
    {q r : ℕ} {tail : List ℕ}
    {family : Set (Embedding
      (Old.toRelStructure.induce (activeCarrier A Old α))
      Large.toRelStructure)}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A
      (Old.toRelStructure.induce (activeCarrier A Old α)))
      (List.replicate (r + 1) (q - 1) ++ tail).length}
    {allowed : Fin
      ((List.replicate (r + 1) (q - 1) ++ tail).length + 1) → Set V}
    (S : ForestTailStage A
      (Old.toRelStructure.induce (activeCarrier A Old α))
      Large.toRelStructure family
      (List.replicate (r + 1) (q - 1) ++ tail)
      targetTrain allowed)
    (hFamilyParts : ∀ b, b ∈ family →
      ∀ x : activeCarrier A Old α,
        Large.part (b x) = activeSourcePart A Old α x) :
    let E := S.system.coarsenVia Large S.isPartite
    let f : {b : DesignatedCopy
      (Old.toRelStructure.induce (activeCarrier A Old α))
      Large.toRelStructure S.system family // b ∈ S.selected} →
        Embedding (Old.toRelStructure.induce (activeCarrier A Old α))
          E.toRelStructure :=
      fun i => (selectedPartiteGluingFamily_of_largeBase
        (actualActiveSubsystemPartite A Old α)
        Large S.system S.isPartite family hFamilyParts
        S.selected i).toEmbedding
    let T := S.train.castHeight (actualReplicatedCutoff_height_eq q r tail)
    ∀ j : Fin (q :: tail).length, 0 < j.val →
      (sharedWitnessOrderOneData
        (T.forgetFirstCuts (by simp : 0 < (q :: tail).length))
        j.castSucc
        (sharedOldACarrierCoreEmbedding A Old.toRelStructure
          (activeCarrier A Old α) E.toRelStructure f)
        (Subtype.val : OldACarrierEdge A E.toRelStructure → Set S.Vertex)
      ).FullSystemGirthGT ((q :: tail).get j) := by
  classical
  let lowerCuts := List.replicate (r + 1) (q - 1) ++ tail
  let E := S.system.coarsenVia Large S.isPartite
  let I := {b : DesignatedCopy
    (Old.toRelStructure.induce (activeCarrier A Old α))
    Large.toRelStructure S.system family // b ∈ S.selected}
  let f : I → Embedding
      (Old.toRelStructure.induce (activeCarrier A Old α))
      E.toRelStructure :=
    fun i => (selectedPartiteGluingFamily_of_largeBase
      (actualActiveSubsystemPartite A Old α)
      Large S.system S.isPartite family hFamilyParts
      S.selected i).toEmbedding
  let m := (q :: tail).length
  have hm : 0 < m := by simp [m]
  have hLen : lowerCuts.length = m + r :=
    actualReplicatedCutoff_height_eq q r tail
  let T := S.train.castHeight hLen
  intro j hj
  let μ : Fin (m + 1) := j.castSucc
  let ν : Fin (m + r + 1) :=
    EdgeTrainLevels.firstForgetIndex m r μ
  have hν : ν.val = j.val + r := by
    simp only [ν, μ, EdgeTrainLevels.firstForgetIndex,
      Nat.ne_of_gt hj, ↓reduceIte]
  let k : Fin lowerCuts.length := ⟨ν.val, by
    rw [hLen]
    have hjLt := j.isLt
    change j.val < m at hjLt
    omega⟩
  have hkPos : 0 < k.val := by
    dsimp [k]
    omega
  let kExpected : Fin lowerCuts.length := ⟨j.val + r, by
    simp only [lowerCuts, List.length_append,
      List.length_replicate, List.length_cons]
    have hjLt := j.isLt
    simp only [List.length_cons] at hjLt
    omega⟩
  have hk : k = kExpected := by
    apply Fin.ext
    exact hν
  have hCutoff : lowerCuts.get k = (q :: tail).get j := by
    rw [hk]
    exact originalPositiveCutoff_eq_lowerRetained q r tail j hj
  have hStage :
      (activeGluingWitnessOrderOneData A Old α
        E.toRelStructure f S.train k.castSucc).FullSystemGirthGT
        ((q :: tail).get j) := by
    have h := S.coarsenedSelected_fullSystem_at_positive
      A Old α Large hFamilyParts k hkPos
    rw [hCutoff] at h
    exact h
  have hIdx :
      Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm ν =
        k.castSucc := Fin.ext rfl
  have hFine :
      (activeGluingWitnessOrderOneData A Old α
        E.toRelStructure f T ν).FullSystemGirthGT
        ((q :: tail).get j) := by
    apply activeGluingWitness_fullSystemGirth_castHeight
      A Old α E.toRelStructure f S.train hLen ν ((q :: tail).get j)
    rw [hIdx]
    exact hStage
  have hCoarse :
      (activeGluingWitnessOrderOneData A Old α
        E.toRelStructure f
        (T.forgetFirstCuts hm) μ).FullSystemGirthGT
        ((q :: tail).get j) :=
    activeGluingWitness_retainedFullSystem_of_fine
      A Old α E.toRelStructure f T hm μ ((q :: tail).get j) hFine
  rw [activeGluingWitnessOrderOneData_eq_shared
    A Old α E.toRelStructure f (T.forgetFirstCuts hm) μ] at hCoarse
  exact hCoarse

end StructuralRamsey.Girth.TrainRecursiveWitness

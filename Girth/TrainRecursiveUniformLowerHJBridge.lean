import Girth.TrainRecursiveUniformPartiteForest
import Girth.TrainRecursiveTrueActiveTargetSupportData
import Girth.TrainRecursiveTrueActiveFineParameters
import Girth.TrainRecursiveTrueActiveLowerCutoffVector
import Girth.TrainRecursiveStrongSupportedHJBase
import Girth.TrainRecursiveExactHeightTransport
import Girth.TrainRecursiveActualHeightCutoffApplication
import Girth.TrainRecursiveTrueActiveTwoCopies

set_option autoImplicit false
set_option Elab.async false

/-!
# The actual smaller-rank universal theorem supplies a selected lower stage

This is the missing rank-interface direction of the nontrivial q>2 step.
The input is one UNIVERSAL selected-partite forest assertion at the
strictly smaller lower cutoff vector. It is not a concrete lower stage,
a current-rank PictureStep, or an arbitrarily assumed output tail bound.

The old stage and first-wagon refinement supply the true active source,
all its physical A-support data, its fine adjacent parameters, and all
positive labelled cuts at the actual lower thresholds. A single supported
Hales--Jewett base supplies the finite large base, its part-preserving
A-strong selected family, and the indexed partite Ramsey input.

Applying the universal lower assertion to exactly these data yields a
real ForestTailStage and its DesignatedArrow. The final outer picture
step can therefore consume this theorem without treating that lower
stage as a free geometric oracle.

This file does not prove the universal assertion itself or discharge the
cutoff-two/forest-to-order operators. Its purpose is to make the q>2
dependency on the STRICTLY SMALLER rank mathematically explicit.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- Apply one universal lower-rank selected forest assertion to the
complete true active source and the genuine first-wagon refinement.
The large Hales--Jewett base is constructed here rather than supplied. -/
theorem ForestTailStage.exists_realSelectedLower_of_uniformRank
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    (B : RelStructure L.withOrder VB)
    (D : RelStructure L.withOrder P)
    {family : Set (Embedding B D)}
    {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (old : ForestTailStage A₀.ordered B D family (q :: tail)
      targetTrain allowed)
    (e : Embedding A₀.ordered D)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered old.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val)
    (ht : Admissible (q :: tail)) (hq : 2 < q)
    (R : FirstWagonRefinement
      (old.train.restrict (sharedOldACarrierInclusion
        A₀.ordered old.system.toRelStructure
        (activeCarrier A₀.ordered old.system e.toFunctionEmbedding)))
      (by simp : 0 < (q :: tail).length)
      (fun edge => edge.1.1) old.system.part
      (allowed ⟨1, by simp⟩) (q - 1))
    (κ : Type w) [Fintype κ] [Nonempty κ]
    (hLower : UniformSelectedPartiteForest A₀
      (List.replicate (R.extraCuts + 1) (q - 1) ++ tail) κ) :
    let Source := actualActiveSubsystemPartite A₀.ordered old.system
      e.toFunctionEmbedding
    ∃ N : ℕ, 0 < N ∧
      let Large := StructuralRamsey.Partite.Induced.power Source N
      Large.IsPartiteOver A₀.ordered ∧
      ∃ lowerFamily : Set (Embedding
        Source.toRelStructure Large.toRelStructure),
        (∀ b, b ∈ lowerFamily → ∀ x : activeCarrier A₀.ordered
          old.system e.toFunctionEmbedding,
          Large.part (b x) = Source.part x) ∧
        (∀ b, b ∈ lowerFamily →
          AStrong A₀.ordered Large.toRelStructure (copyCarrier b)) ∧
        ∃ lower : ForestTailStage A₀.ordered Source.toRelStructure
          Large.toRelStructure lowerFamily
          (List.replicate (R.extraCuts + 1) (q - 1) ++ tail)
          ((R.train.restrict (inducedACarrierToShared A₀.ordered
            old.system.toRelStructure
            (activeCarrier A₀.ordered old.system e.toFunctionEmbedding))).castHeight
            (actualReplicatedCutoff_height_eq q R.extraCuts tail).symm)
          (fun ρ => Large.part ⁻¹'
            (fineAllowedFromRefinement
              (q :: tail).length R.extraCuts
              (by simp : 0 < (q :: tail).length)
              e.toFunctionEmbedding allowed R.permitted
              (Fin.cast (congrArg (fun k : ℕ => k + 1)
                (actualReplicatedCutoff_height_eq q R.extraCuts tail)) ρ))),
          DesignatedArrow lower κ := by
  classical
  let A := A₀.ordered
  let Source := actualActiveSubsystemPartite A old.system e.toFunctionEmbedding
  let m := (q :: tail).length
  have hm : 0 < m := Nat.zero_lt_succ _
  let d := R.extraCuts
  let lowerCuts := List.replicate (d + 1) (q - 1) ++ tail
  have hLen : lowerCuts.length = m + d :=
    actualReplicatedCutoff_height_eq q d tail
  let sourceFine := R.train.restrict
    (inducedACarrierToShared A old.system.toRelStructure
      (activeCarrier A old.system e.toFunctionEmbedding))
  let lowerTrain := sourceFine.castHeight hLen.symm
  let fineAllowed := fineAllowedFromRefinement m d hm
    e.toFunctionEmbedding allowed R.permitted
  let lowerAllowed : Fin (lowerCuts.length + 1) → Set UA :=
    fun ρ => fineAllowed (Fin.cast
      (congrArg (fun k : ℕ => k + 1) hLen) ρ)
  letI : Finite old.Vertex := old.finiteVertex
  have hGeometry := ForestTailStage.trueActive_HJ_sourceGeometry
    A B D old e
  have hSourcePartite : Source.IsPartiteOver A := hGeometry.1
  have hSourceLinear : ALinear A Source.toRelStructure := hGeometry.2.1
  have hSourceCovers : ∀ x : activeCarrier A old.system
      e.toFunctionEmbedding, ∃ a : Embedding A Source.toRelStructure,
      x ∈ copyCarrier a := hGeometry.2.2
  let projected : StructuralRamsey.Partite.ProjectedEmbedding
      A old.system e.toFunctionEmbedding := Classical.choose hPair
  have hTargetTwo : ∃ a b : Embedding A Source.toRelStructure,
      ¬ SameCopy a b :=
    activeTarget_twoGenuineCopies_of_nontrivialFibre
      A old.system e.toFunctionEmbedding hPair
  obtain ⟨hPhysical, hCovers, hGirthOld⟩ :=
    old.trueActive_initialSupportData e projected (q - 1) (by
      change q - 1 ≤ q
      omega)
  have hLowerHead : lowerCuts.headD 0 = q - 1 := by
    simp [lowerCuts, List.replicate_succ]
  have hGirth : GirthGT
      (supportCopies A Source.toRelStructure) (lowerCuts.headD 0) := by
    rw [hLowerHead]
    exact hGirthOld
  have hFineParams :=
    old.trueActive_inducedRefinementAdjacentParameters e hm R
  have hIndex (ρ : Fin (lowerCuts.length + 1)) :
      Fin.cast (congrArg (fun k : ℕ => k + 1) hLen.symm).symm ρ =
        Fin.cast (congrArg (fun k : ℕ => k + 1) hLen) ρ :=
    Fin.ext rfl
  have hParams : lowerTrain.AdjacentParameters
      (fun edge => edge.1)
      (fun ρ => Source.part ⁻¹' lowerAllowed ρ) := by
    have hTransport := sourceFine.castHeight_adjacentParameters
      (fun edge => edge.1) hLen.symm
      (fun ν => Source.part ⁻¹' fineAllowed ν) hFineParams
    simpa only [hIndex] using hTransport
  have hCuts : ∀ j : Fin lowerCuts.length, 0 < j.val →
      LabelledGirthGT
        (lowerTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        (lowerCuts.get j) := by
    intro j hj
    let jFine : Fin (m + d) := Fin.cast hLen j
    have hFine := old.trueActive_inducedAllLowerCutGirth
      e ht hq R jFine (by exact hj)
    have hCutIndex :
        Fin.cast (congrArg (fun k : ℕ => k + 1) hLen.symm).symm
          j.castSucc = jFine.castSucc := Fin.ext rfl
    have hOne : LabelledGirthGT
        (sourceFine.wagonClassCarrier (fun edge => edge.1)
          (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen.symm).symm
            j.castSucc))
        (lowerCuts.get j) := by
      rw [hCutIndex]
      convert hFine using 1
      exact congrArg (List.get lowerCuts) (Fin.ext rfl)
    exact sourceFine.castHeight_labelledCutGirth
      (fun edge => edge.1) hLen.symm j.castSucc (lowerCuts.get j) hOne
  have hLowerAdmissible : Admissible lowerCuts :=
    ht.replace hq (Nat.succ_pos d)
  obtain ⟨N, hN, hLargePartite, hLargeLinear, _hLargeCovers,
      lowerFamily, _hFamilyNonempty, hParts, hStrong, hHJArrow⟩ :=
    exists_largeBase_strongSupportedHJLineRamseyFamily
      A₀ Source hSourcePartite hSourceLinear hSourceCovers κ
  let Large := StructuralRamsey.Partite.Induced.power Source N
  have hFamilyArrow :
      ∀ χ : StructuralRamsey.Partite.Embedding
          (StructuralRamsey.Partite.transversal A) Large → κ,
        ∃ b : StructuralRamsey.Partite.Embedding Source Large,
          b.toEmbedding ∈ lowerFamily ∧
          ∀ a₁ a₂ : StructuralRamsey.Partite.Embedding
            (StructuralRamsey.Partite.transversal A) Source,
            χ (b.comp a₁) = χ (b.comp a₂) := by
    intro χ
    obtain ⟨W, hW, hMono⟩ := hHJArrow χ
    exact ⟨StructuralRamsey.Partite.Induced.lineEmbedding
      hSourcePartite W, hW, hMono⟩
  have hFinal := hLower Source Large lowerFamily
    hLowerAdmissible hSourcePartite hSourceLinear hTargetTwo
    hLargePartite hLargeLinear hStrong hParts
    lowerTrain lowerAllowed hPhysical hCovers hGirth
    hParams hCuts hFamilyArrow
  exact ⟨N, hN, hLargePartite, lowerFamily, hParts, hStrong, hFinal⟩

end StructuralRamsey.Girth.TrainRecursiveWitness

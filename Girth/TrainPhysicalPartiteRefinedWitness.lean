import Girth.TrainPhysicalPartiteForestData
import Girth.TrainRecursiveFineWitnessBounds
import Girth.TrainRecursiveExactRetainedFullSystemGirth
import Girth.TrainRecursiveActualFullSystemHeightTransport
import Girth.TrainRecursiveActualHeightCutoffApplication
import Girth.TrainRecursiveCanonicalFineAllowed

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA P X : Type v}
variable (A : RelStructure L UA)
variable (Old : StructuralRamsey.Partite.System L P X) (α : UA ↪ P)
variable {q : ℕ} {tail : List ℕ}
variable (train : EdgeTrainLevels (OldACarrierEdge A Old.toRelStructure) (q :: tail).length)
variable (allowed : Fin ((q :: tail).length + 1) → Set P)

/-- A refinement of the first retained wagon of the physical active train. -/
abbrev ActiveFirstWagonRefinement :=
  FirstWagonRefinement
    (train.restrict (sharedOldACarrierInclusion A Old.toRelStructure (activeCarrier A Old α)))
    (by simp : 0 < (q :: tail).length) (fun edge => edge.1.1) Old.part
    (allowed ⟨1, by simp⟩) (q - 1)

variable (R : ActiveFirstWagonRefinement (q := q) (tail := tail) A Old α train allowed)

/-- The literal lower vector and source data of the true active refinement. -/
abbrev RefinedFineWitness (κ : Type w) :=
  FinePartiteFtWitness A (actualActiveSubsystemPartite A Old α)
    (List.replicate (R.extraCuts + 1) (q - 1) ++ tail)
    ((R.train.restrict
      (inducedACarrierToShared A Old.toRelStructure (activeCarrier A Old α))).castHeight
        (actualReplicatedCutoff_height_eq q R.extraCuts tail).symm)
    (fun ν => fineAllowedFromRefinement (q :: tail).length R.extraCuts (by simp)
      α allowed R.permitted
      (Fin.cast (congrArg (fun n : ℕ => n + 1)
        (actualReplicatedCutoff_height_eq q R.extraCuts tail)) ν)) κ

variable {κ : Type w}

/-- The genuine selected train in the refinement's height coordinates. -/
abbrev FinePartiteFtWitness.refinedTrain (W : RefinedFineWitness (q := q) (tail := tail) A Old α train allowed R κ) :=
  W.train.castHeight (actualReplicatedCutoff_height_eq q R.extraCuts tail)

/-- Retain all physical labels and exactly the old train cuts. -/
abbrev FinePartiteFtWitness.coarseTrain (W : RefinedFineWitness (q := q) (tail := tail) A Old α train allowed R κ) :=
  (W.refinedTrain A Old α train allowed R).forgetFirstCuts (by simp : 0 < (q :: tail).length)

private theorem castHeight_rel_iff {E : Type v} {a b : ℕ}
    (F : EdgeTrainLevels E a) (h : a = b) (ν : Fin (b + 1)) (x y : E) :
    (F.castHeight h).rel ν x y ↔
      F.rel (Fin.cast (congrArg (fun n : ℕ => n + 1) h).symm ν) x y := by
  cases h
  rfl

/-- Changing the height expression preserves the relation on every actual
selected lift at every fine cut. -/
theorem FinePartiteFtWitness.refinedRestriction
    (W : RefinedFineWitness (q := q) (tail := tail) A Old α train allowed R κ)
    (ν : Fin ((q :: tail).length + R.extraCuts + 1)) (i : W.Index)
    (a b : Embedding A (actualActiveSubsystemPartite A Old α).toRelStructure) :
    (W.refinedTrain A Old α train allowed R).rel ν
      (actualEdge ((W.selected i).toEmbedding.comp a))
      (actualEdge ((W.selected i).toEmbedding.comp b)) ↔
    (R.train.restrict
      (inducedACarrierToShared A Old.toRelStructure (activeCarrier A Old α))).rel ν
      (actualEdge a) (actualEdge b) := by
  let source := R.train.restrict
    (inducedACarrierToShared A Old.toRelStructure (activeCarrier A Old α))
  let hLen := actualReplicatedCutoff_height_eq q R.extraCuts tail
  let ρ := Fin.cast (congrArg (fun n : ℕ => n + 1) hLen).symm ν
  have hBack : (source.castHeight hLen.symm).rel ρ (actualEdge a) (actualEdge b) ↔
      source.rel ν (actualEdge a) (actualEdge b) := by
    have hIndex : Fin.cast (congrArg (fun n : ℕ => n + 1) hLen.symm).symm ρ = ν :=
      Fin.ext rfl
    simpa only [hIndex] using
      castHeight_rel_iff source hLen.symm ρ (actualEdge a) (actualEdge b)
  exact (castHeight_rel_iff W.train hLen ν
    (actualEdge ((W.selected i).toEmbedding.comp a))
    (actualEdge ((W.selected i).toEmbedding.comp b))).trans
      ((W.selectedTrain ρ i a b).trans hBack)

theorem FinePartiteFtWitness.refinedParameters
    (W : RefinedFineWitness (q := q) (tail := tail) A Old α train allowed R κ) :
    (W.refinedTrain A Old α train allowed R).AdjacentParameters (fun edge => edge.1)
      (fun ν => W.core.part ⁻¹'
        fineAllowedFromRefinement (q :: tail).length R.extraCuts (by simp) α allowed R.permitted ν) := by
  let hLen := actualReplicatedCutoff_height_eq q R.extraCuts tail
  let fineAllowed := fineAllowedFromRefinement (q :: tail).length R.extraCuts (by simp)
    α allowed R.permitted
  have h := W.train.castHeight_adjacentParameters (fun edge => edge.1) hLen
    (fun ν => W.core.part ⁻¹' fineAllowed
      (Fin.cast (congrArg (fun n : ℕ => n + 1) hLen) ν)) W.fineParameters
  have hAllowed (ν : Fin ((q :: tail).length + R.extraCuts + 1)) :
      Fin.cast (congrArg (fun n : ℕ => n + 1) hLen)
        (Fin.cast (congrArg (fun n : ℕ => n + 1) hLen).symm ν) = ν :=
    Fin.ext rfl
  simpa only [hAllowed] using h

/-- The relabelled coarse train keeps the exact source relations and
adjacent intersection parameters. -/
theorem FinePartiteFtWitness.refinedCoarseTrain
    (W : RefinedFineWitness (q := q) (tail := tail) A Old α train allowed R κ) :
    (∀ (μ : Fin ((q :: tail).length + 1)) (i : W.Index)
      (p r : SharedOldACarrierEdge A Old.toRelStructure (activeCarrier A Old α)),
      train.rel μ p.1 r.1 ↔ (W.coarseTrain A Old α train allowed R).rel μ
        (sharedOldACarrierCoreEmbedding A Old.toRelStructure (activeCarrier A Old α)
          (W.core.relabel α).toRelStructure (fun i : W.Index => (W.selected i).toEmbedding) i p)
        (sharedOldACarrierCoreEmbedding A Old.toRelStructure (activeCarrier A Old α)
          (W.core.relabel α).toRelStructure (fun i : W.Index => (W.selected i).toEmbedding) i r)) ∧
    (W.coarseTrain A Old α train allowed R).AdjacentParameters (fun edge => edge.1)
      (fun ν => (W.core.relabel α).part ⁻¹' allowed ν) := by
  let T := W.refinedTrain A Old α train allowed R
  let f := fun i : W.Index => (W.selected i).toEmbedding
  have hm : 0 < (q :: tail).length := by simp
  let fineAllowed := fineAllowedFromRefinement (q :: tail).length R.extraCuts hm α allowed R.permitted
  have hAllowed := fineAllowedFromRefinement_all_constraints (q :: tail).length R.extraCuts
    hm α allowed R.permitted R.permitted_subset R.permitted_subsingleton
  exact ⟨fun μ i p r => coarseSharedTrain_iff_of_finePrescribedRestriction
      A Old.toRelStructure (activeCarrier A Old α) (W.core.relabel α).toRelStructure f train hm R T
      (W.refinedRestriction A Old α train allowed R) μ i p r,
    relabelledCore_forgetFirstCuts_adjacentParameters A α W.core T hm fineAllowed allowed
      (W.refinedParameters A Old α train allowed R) hAllowed.2.1 hAllowed.2.2⟩

/-- On the refined witness, the mixed budget is the lower vector's head,
which is exactly the predecessor of the old head. -/
theorem FinePartiteFtWitness.refinedMixedForest
    (W : RefinedFineWitness (q := q) (tail := tail) A Old α train allowed R κ) :
    FiniteMixedForestThrough
      (RelationalMixedSupportTest A (fun i : W.Index => (W.selected i).toEmbedding)) (q - 1) := by
  simpa [List.replicate_succ] using W.mixedForest

/-- At a positive fine cut, the height cast retains the actual incidence
and the exact entry of the lower cutoff vector. -/
theorem FinePartiteFtWitness.refinedFullAt
    (W : RefinedFineWitness (q := q) (tail := tail) A Old α train allowed R κ)
    (ν : Fin ((q :: tail).length + R.extraCuts + 1)) (hPos : 0 < ν.val)
    (hLt : ν.val < (q :: tail).length + R.extraCuts) :
    OrderOneData.FullSystemGirthGT (activeGluingWitnessOrderOneData A Old α W.core.toRelStructure
      (fun i : W.Index => (W.selected i).toEmbedding) (W.refinedTrain A Old α train allowed R) ν)
      ((List.replicate (R.extraCuts + 1) (q - 1) ++ tail).get
        ⟨ν.val, by rwa [actualReplicatedCutoff_height_eq]⟩) := by
  let hLen := actualReplicatedCutoff_height_eq q R.extraCuts tail
  let k : Fin (List.replicate (R.extraCuts + 1) (q - 1) ++ tail).length :=
    ⟨ν.val, by rwa [hLen]⟩
  have hIndex : Fin.cast (congrArg (fun n : ℕ => n + 1) hLen).symm ν = k.castSucc := Fin.ext rfl
  apply activeGluingWitness_fullSystemGirth_castHeight A Old α W.core.toRelStructure
    (fun i : W.Index => (W.selected i).toEmbedding) W.train hLen
  rw [hIndex]
  exact W.positiveFull k hPos

/-- The refined witness has cutoff q-1 on the inserted cuts and at least
q at every positive proper retained cut. -/
theorem FinePartiteFtWitness.refinedFull
    (W : RefinedFineWitness (q := q) (tail := tail) A Old α train allowed R κ)
    (hMono : (q :: tail).Pairwise (· ≤ ·))
    (ν : Fin ((q :: tail).length + R.extraCuts + 1)) (hPos : 0 < ν.val)
    (hLt : ν.val < (q :: tail).length + R.extraCuts) :
    OrderOneData.FullSystemGirthGT (activeGluingWitnessOrderOneData A Old α W.core.toRelStructure
      (fun i : W.Index => (W.selected i).toEmbedding) (W.refinedTrain A Old α train allowed R) ν)
      (if ν.val ≤ R.extraCuts then q - 1 else q) := by
  let lower := List.replicate (R.extraCuts + 1) (q - 1) ++ tail
  have hLen : lower.length = (q :: tail).length + R.extraCuts :=
    actualReplicatedCutoff_height_eq q R.extraCuts tail
  let k : Fin lower.length := ⟨ν.val, by rwa [hLen]⟩
  have hBudget : (if ν.val ≤ R.extraCuts then q - 1 else q) ≤ lower.get k := by
    by_cases hSmall : ν.val ≤ R.extraCuts
    · let j : Fin (R.extraCuts + 1) := ⟨ν.val, Nat.lt_succ_of_le hSmall⟩
      have hEq : lower.get k = q - 1 :=
        replicatedCutoff_at_inserted (q - 1) (R.extraCuts + 1) tail j
      simpa only [if_pos hSmall, hEq] using Nat.le_refl (q - 1)
    · have hOldLt : ν.val - R.extraCuts < (q :: tail).length := by omega
      let j : Fin (q :: tail).length := ⟨ν.val - R.extraCuts, hOldLt⟩
      have hOldPos : 0 < j.val := by change 0 < ν.val - R.extraCuts; omega
      have hIndexLt : j.val + R.extraCuts < lower.length := by
        rw [hLen]
        exact Nat.add_lt_add_right j.isLt R.extraCuts
      have hIdx : (⟨j.val + R.extraCuts, hIndexLt⟩ : Fin lower.length) = k := by
        apply Fin.ext
        change ν.val - R.extraCuts + R.extraCuts = ν.val
        omega
      have hEq := actualReplicatedCutoff_retainedValue q R.extraCuts tail j hOldPos
      rw [hIdx] at hEq
      change lower.get k = (q :: tail).get j at hEq
      have hLe : q ≤ (q :: tail).get j := by
        let i : Fin tail.length := ⟨j.val - 1, by
          have h := j.isLt
          simp only [List.length_cons] at h
          omega⟩
        have hFin : j = (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (q :: tail).length) := by
          apply Fin.ext
          change j.val = j.val - 1 + 1
          omega
        rw [hFin]
        exact (List.pairwise_cons.mp hMono).1 (tail.get i) (List.get_mem tail i)
      simpa only [if_neg hSmall, hEq] using hLe
  obtain ⟨hLinear, hSupreme⟩ := W.refinedFullAt A Old α train allowed R ν hPos hLt
  exact ⟨hLinear, fun n cycle hAccept hOrder =>
    hSupreme n cycle hAccept (le_trans hOrder (Nat.mul_le_mul_left 2 hBudget))⟩

/-- The whole selected-copy incidence system survives at each retained
positive cut, with the exact old tail cutoff. -/
theorem FinePartiteFtWitness.refinedRetainedFull
    (W : RefinedFineWitness (q := q) (tail := tail) A Old α train allowed R κ)
    (j : Fin (q :: tail).length) (hj : 0 < j.val) :
    OrderOneData.FullSystemGirthGT
      (activeGluingWitnessOrderOneData A Old α (W.core.relabel α).toRelStructure
        (fun i : W.Index => (W.selected i).toEmbedding)
        (W.coarseTrain A Old α train allowed R) j.castSucc) ((q :: tail).get j) := by
  let lower := List.replicate (R.extraCuts + 1) (q - 1) ++ tail
  have hLen : lower.length = (q :: tail).length + R.extraCuts :=
    actualReplicatedCutoff_height_eq q R.extraCuts tail
  let k : Fin lower.length :=
    ⟨j.val + R.extraCuts, by rw [hLen]; exact Nat.add_lt_add_right j.isLt R.extraCuts⟩
  apply activeGluingWitness_retainedFullSystem_of_fine A Old α (W.core.relabel α).toRelStructure
    (fun i : W.Index => (W.selected i).toEmbedding) (W.refinedTrain A Old α train allowed R)
    (by simp : 0 < (q :: tail).length)
  let ν := EdgeTrainLevels.firstForgetIndex (q :: tail).length R.extraCuts j.castSucc
  have hν : ν.val = j.val + R.extraCuts := by
    simp [ν, EdgeTrainLevels.firstForgetIndex, Nat.ne_of_gt hj]
  have hPos : 0 < ν.val := by omega
  have hLt : ν.val < (q :: tail).length + R.extraCuts := by have h := j.isLt; omega
  have hIdx : (⟨ν.val, by rwa [hLen]⟩ : Fin lower.length) = k := Fin.ext hν
  have hCut : lower.get k = (q :: tail).get j :=
    actualReplicatedCutoff_retainedValue q R.extraCuts tail j hj
  have hFull := W.refinedFullAt A Old α train allowed R ν hPos hLt
  rw [hIdx] at hFull
  change OrderOneData.FullSystemGirthGT
    (activeGluingWitnessOrderOneData A Old α W.core.toRelStructure
      (fun i : W.Index => (W.selected i).toEmbedding)
      (W.refinedTrain A Old α train allowed R) ν) (lower.get k) at hFull
  rw [hCut] at hFull
  exact hFull

/-- The lower mixed forest and the refined positive cuts give ordinary
girth at the old head on the entire local physical support. -/
theorem FinePartiteFtWitness.refinedCoreGirth
    (W : RefinedFineWitness (q := q) (tail := tail) A Old α train allowed R κ) (hA : A.Irreducible) (hq : 2 < q)
    (hMono : (q :: tail).Pairwise (· ≤ ·)) :
    GirthGT (supportCopies A (W.core.relabel α).toRelStructure) q := by
  have hm : 0 < (q :: tail).length := by simp
  let fineAllowed := fineAllowedFromRefinement (q :: tail).length R.extraCuts hm α allowed R.permitted
  exact activeFineWitness_supportGirth A hA Old α W.core W.selected hm hq
    (W.refinedTrain A Old α train allowed R) fineAllowed (W.refinedParameters A Old α train allowed R)
    (fineAllowedFromRefinement_parent_subsingleton (q :: tail).length R.extraCuts hm α allowed
      R.permitted R.permitted_subsingleton)
    (W.refinedMixedForest A Old α train allowed R)
    (W.refinedFull A Old α train allowed R hMono)

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

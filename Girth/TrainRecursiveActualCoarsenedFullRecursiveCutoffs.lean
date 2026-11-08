import Girth.TrainRecursiveActualCoarsenedFullSystem
import Girth.TrainRecursiveCutoffIndexAlignment
import Girth.TrainRecursiveExactHeightTransport

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual selected gluing full-system girth at the precise recursive cutoffs

The q>2 local fine witness uses the lower cutoff vector
  replicate d (q-1) ++ tail
where d=R.extraCuts+1. The genuine lower selected forest stage has
FullSystemGirthGT at each positive proper cut with the LITERAL value
of that vector. The physical gluing labels are exactly the selected
designated-copy subtype, with no equal-carrier quotient.

The old request q::tail is nondecreasing. Hence the FULL output
gluing system has required cutoff q-1 on all newly inserted cuts,
and cutoff q at every retained interior cut. Both bounds follow from
the lower stage's own tailGirth via the exact selected-gluing theorem,
with no additional local hFull assumption. This is genuine global
simultaneous replacement girth, NOT merely edge girth or a local
bridge bound. The resulting cutoffs match the hFull input in the
nontrivial first-wagon refinement step.

This theorem still assumes the actual selected LOWER ForestTailStage
(and part-preservation of its designated base family), which the
recursive induction has to construct; it does not supply the
attached-output SupremeCycleBound or the lower Ramsey picture pass.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P V X : Type v}
variable (A : RelStructure L UA)
variable (Old : StructuralRamsey.Partite.System L P X)
variable (α : UA ↪ P)
variable (D : StructuralRamsey.Partite.System L UA V)


variable {q d : ℕ} {tail : List ℕ}
variable {family : Set (Embedding (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure)}
variable {targetTrain : EdgeTrainLevels
  (OldACarrierEdge A (Old.toRelStructure.induce (activeCarrier A Old α)))
  (List.replicate d (q - 1) ++ tail).length}
variable {allowed :
  Fin ((List.replicate d (q - 1) ++ tail).length + 1) → Set V}
variable (S : ForestTailStage A (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure family
  (List.replicate d (q - 1) ++ tail) targetTrain allowed)
variable (hFamilyParts : ∀ b, b ∈ family →
  ∀ x : activeCarrier A Old α,
    D.part (b x) = activeSourcePart A Old α x)

include hFamilyParts

/-- The complete PHYSICAL gluing full-system certificate at every
positive proper fine cut, at exactly the q-1/q thresholds required by
the actual first-wagon refinement attachment. No independent hFull
input or artificially assumed girth of a Hales--Jewett power. -/
theorem ForestTailStage.coarsenedSelected_fullSystem_for_recursiveCuts
    (hMonotone : (q :: tail).Pairwise (· ≤ ·))
    (ν : Fin ((List.replicate d (q - 1) ++ tail).length + 1))
    (hPos : 0 < ν.val)
    (hInterior : ν.val < (List.replicate d (q - 1) ++ tail).length) :
    (activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      (fun i : {b : DesignatedCopy (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure S.system family //
          b ∈ S.selected} =>
        (selectedPartiteGluingFamily_of_largeBase
          (actualActiveSubsystemPartite A Old α) D S.system S.isPartite family hFamilyParts
          S.selected i).toEmbedding)
      S.train ν).FullSystemGirthGT
        (if ν.val < d then q - 1 else q) := by
  let lower := List.replicate d (q - 1) ++ tail
  let j : Fin lower.length := ⟨ν.val, hInterior⟩
  have hjPos : 0 < j.val := hPos
  have hLevel : j.castSucc = ν := by
    apply Fin.ext
    rfl
  have hBudget : (if ν.val < d then q - 1 else q) ≤ lower.get j := by
    by_cases hSmall : ν.val < d
    · let k : Fin d := ⟨ν.val, hSmall⟩
      have hIdx : (⟨k.val, by
          simp only [lower, List.length_append, List.length_replicate]
          have hk := k.isLt
          omega⟩ : Fin lower.length) = j := by
        apply Fin.ext
        rfl
      have hAt := replicatedCutoff_at_inserted (q - 1) d tail k
      have hEq : lower.get j = q - 1 := by
        simpa only [lower, hIdx] using hAt
      simpa only [if_pos hSmall, hEq] using Nat.le_refl (q - 1)
    · have hLarge : d ≤ ν.val := Nat.le_of_not_lt hSmall
      let k : Fin tail.length := ⟨ν.val - d, by
        have hLt := hInterior
        simp only [List.length_append, List.length_replicate] at hLt
        omega⟩
      have hIdx : (⟨d + k.val, by
          simp only [lower, List.length_append, List.length_replicate]
          have hk := k.isLt
          omega⟩ : Fin lower.length) = j := by
        apply Fin.ext
        change d + (ν.val - d) = ν.val
        omega
      have hTail := replicatedCutoff_retained_ge
        q (q - 1) d tail hMonotone k
      have hBound : q ≤ lower.get j := by
        simpa only [lower, hIdx] using hTail
      simpa only [if_neg hSmall] using hBound
  have hFull := S.coarsenedSelected_fullSystem_at_positive_mono
    A Old α D hFamilyParts j hjPos
    (if ν.val < d then q - 1 else q) hBudget
  simpa only [hLevel] using hFull

/-- Restate the same genuine full-system certificate in the precise
`ν ≤ extraCuts` form consumed by the refining-picture-step API.
This is only an index conversion, not an additional girth assumption. -/
theorem ForestTailStage.coarsenedSelected_fullSystem_for_attachmentBudget
    (r : ℕ) (hd : d = r + 1)
    (hMonotone : (q :: tail).Pairwise (· ≤ ·))
    (ν : Fin ((List.replicate d (q - 1) ++ tail).length + 1))
    (hPos : 0 < ν.val)
    (hInterior : ν.val < (List.replicate d (q - 1) ++ tail).length) :
    (activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      (fun i : {b : DesignatedCopy (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure S.system family //
          b ∈ S.selected} =>
        (selectedPartiteGluingFamily_of_largeBase
          (actualActiveSubsystemPartite A Old α) D S.system S.isPartite family hFamilyParts
          S.selected i).toEmbedding)
      S.train ν).FullSystemGirthGT
        (if ν.val ≤ r then q - 1 else q) := by
  have hFull := S.coarsenedSelected_fullSystem_for_recursiveCuts
    A Old α D hFamilyParts hMonotone ν hPos hInterior
  have hBudget :
      (if ν.val < d then q - 1 else q) =
        (if ν.val ≤ r then q - 1 else q) := by
    simp only [hd, Nat.lt_succ_iff]
  rw [← hBudget]
  exact hFull

/-- Exact height-transport into the old attachment API. The selected
physical gluing family, all A-support edges and all wagon labels
remain unchanged; only the Nat height index and its Fin coordinates
are transported along the genuine arithmetic equality. -/
theorem ForestTailStage.coarsenedSelected_fullSystem_for_attachmentHeight
    {m r : ℕ}
    (hLen : m = (List.replicate d (q - 1) ++ tail).length)
    (hd : d = r + 1)
    (hMonotone : (q :: tail).Pairwise (· ≤ ·))
    (ν : Fin (m + 1))
    (hPos : 0 < ν.val)
    (hInterior : ν.val < m) :
    (activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      (fun i : {b : DesignatedCopy (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure S.system family //
          b ∈ S.selected} =>
        (selectedPartiteGluingFamily_of_largeBase
          (actualActiveSubsystemPartite A Old α) D S.system S.isPartite family hFamilyParts
          S.selected i).toEmbedding)
      (S.train.castHeight hLen.symm) ν).FullSystemGirthGT
        (if ν.val ≤ r then q - 1 else q) := by
  cases hLen
  simpa only [EdgeTrainLevels.castHeight_rfl] using
    S.coarsenedSelected_fullSystem_for_attachmentBudget
      A Old α D hFamilyParts r hd hMonotone ν hPos hInterior

end StructuralRamsey.Girth.TrainRecursiveWitness

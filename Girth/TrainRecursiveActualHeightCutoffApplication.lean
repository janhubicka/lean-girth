import Girth.TrainRecursiveActualCoarsenedFullRecursiveCutoffs

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact original-to-lower cutoff height with no supplied numerical cast

In the genuine q>2 recursion the old vector is q :: tail and the
new lower vector is replicate (extraCuts+1) (q-1) ++ tail. Their
train-height equality is derived by elementary list arithmetic, not
an input hypothesis. Apply the selected lower stage's own positive
full-system-girth certificates at precisely the original attachment
height (length (q::tail) + extraCuts) and required q-1/q bounds.

No proof here supplies a selected lower stage, a nontrivial local
refining PictureStep, or the output SupremeCycleBound. All complete
physical gluing edges and selected-copy labels are unchanged.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P V X : Type v}

/-- Equality of the actual original refinement-train height and the
shorter selected recursion's replicated cutoff-vector height. No
additional arithmetic assumption is needed. -/
theorem actualReplicatedCutoff_height_eq (q r : ℕ) (tail : List ℕ) :
    (List.replicate (r + 1) (q - 1) ++ tail).length =
      (q :: tail).length + r := by
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- Every ORIGINAL positive old cutoff retains its exact value at
the genuinely corresponding fine cut: old j becomes fine j+r after
inserting r first-wagon refinement levels. In particular the retained
tail bound is the entire original t_j, not merely the leading q. -/
theorem actualReplicatedCutoff_retainedValue
    (q r : ℕ) (tail : List ℕ)
    (j : Fin (q :: tail).length) (hj : 0 < j.val) :
    (List.replicate (r + 1) (q - 1) ++ tail).get
      ⟨j.val + r, by
        have hlt := j.isLt
        simp only [List.length_cons] at hlt
        simp only [List.length_append, List.length_replicate]
        omega⟩ =
      (q :: tail).get j := by
  let k : Fin tail.length := ⟨j.val - 1, by
    have hlt := j.isLt
    simp only [List.length_cons] at hlt
    omega⟩
  have hjEq : j = (Fin.succ k : Fin (q :: tail).length) := by
    apply Fin.ext
    change j.val = (j.val - 1) + 1
    omega
  have hIndex :
      (⟨j.val + r, by
        have hlt := j.isLt
        simp only [List.length_cons] at hlt
        simp only [List.length_append, List.length_replicate]
        omega⟩ : Fin (List.replicate (r + 1) (q - 1) ++ tail).length) =
      ⟨(r + 1) + k.val, by
        simp only [List.length_append, List.length_replicate]
        exact Nat.add_lt_add_left k.isLt (r + 1)⟩ := by
    apply Fin.ext
    change j.val + r = (r + 1) + (j.val - 1)
    omega
  rw [hIndex, replicatedCutoff_at_retained (q - 1) (r + 1) tail k]
  rw [hjEq]
  rfl

variable (A : RelStructure L UA)
variable (Old : StructuralRamsey.Partite.System L P X)
variable (α : UA ↪ P)
variable (D : StructuralRamsey.Partite.System L UA V)

variable {q r : ℕ} {tail : List ℕ}
variable {family : Set (Embedding (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure)}
variable {targetTrain : EdgeTrainLevels
  (OldACarrierEdge A (Old.toRelStructure.induce (activeCarrier A Old α)))
  (List.replicate (r + 1) (q - 1) ++ tail).length}
variable {allowed :
  Fin ((List.replicate (r + 1) (q - 1) ++ tail).length + 1) → Set V}
variable (S : ForestTailStage A (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure family
  (List.replicate (r + 1) (q - 1) ++ tail) targetTrain allowed)
variable (hFamilyParts : ∀ b, b ∈ family →
  ∀ x : activeCarrier A Old α,
    D.part (b x) = activeSourcePart A Old α x)

include hFamilyParts

/-- The actual full physical gluing family at each positive interior
cut of the original refinement height has exactly the needed cutoff,
q-1 on inserted levels and q on retained levels, with NO independent
height-cast certificate. This is the literal hFull shape in the
nontrivial-fibre picture-step interface. -/
theorem ForestTailStage.coarsenedSelected_fullSystem_for_actualHeight
    (hMonotone : (q :: tail).Pairwise (· ≤ ·))
    (ν : Fin ((q :: tail).length + r + 1))
    (hPos : 0 < ν.val)
    (hInterior : ν.val < (q :: tail).length + r) :
    (activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      (fun i : {b : DesignatedCopy (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure S.system family //
          b ∈ S.selected} =>
        (selectedPartiteGluingFamily_of_largeBase
          (actualActiveSubsystemPartite A Old α) D S.system S.isPartite family hFamilyParts
          S.selected i).toEmbedding)
      (S.train.castHeight
        (actualReplicatedCutoff_height_eq q r tail)) ν).FullSystemGirthGT
        (if ν.val ≤ r then q - 1 else q) := by
  exact S.coarsenedSelected_fullSystem_for_attachmentHeight
    A Old α D hFamilyParts
    (actualReplicatedCutoff_height_eq q r tail).symm
    rfl hMonotone ν hPos hInterior

end StructuralRamsey.Girth.TrainRecursiveWitness

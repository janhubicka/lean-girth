import Girth.TrainRecursiveActualSelectedCoreGirth
import Girth.TrainRecursiveSelectedLowerActualInputs
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Canonical lower selected stage has physical core girth without free fine geometry

The true q > 2 local recursion uses the old FirstWagonRefinement R and the
literal lower cutoff list replicate (R.extraCuts + 1) (q - 1) ++ tail.
The lower stage is assumed to be a GENUINE ForestTailStage with its allowed
large-base vertex parts equal to the canonical fineAllowedFromRefinement
pulled back along the large-base part map.

The independently audited actual-lower core theorem derives the selected
mixed forest, complete adjacent parameters, and the positive q-1/q
FullSystemGirthGT certificates from precisely this actual lower stage.
Its remaining singleton fine-parent hypothesis follows from the real
R.permitted_subsingleton field via
FirstWagonRefinement.canonicalFineAllowed_all_constraints.

No original A-support edge, selected label, full-system wagon quotient or
tail cutoff is changed. In particular, no girth of a Hales--Jewett
power, constructed recursive lower-stage arrow or attached-output
SupremeCycleBound is postulated. This is circulation only.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P Q E W : Type v}

private theorem canonicalActualLowerHeight (q d : ℕ) (tail : List ℕ) :
    (q :: tail).length + d =
      (List.replicate (d + 1) (q - 1) ++ tail).length := by
  simp only [List.length_cons, List.length_append, List.length_replicate]
  omega

/-- In a real first-wagon refinement, the canonical fine A-parts
are singleton at EVERY inserted parent, including the overlapping
first retained parent, after exact transport to the lower list height.
-/
theorem FirstWagonRefinement.canonicalLowerParent_subsingleton
    {m : ℕ} {T : EdgeTrainLevels E m} {hm : 0 < m}
    {edge : E → Set W} {part : W → P} {g : ℕ}
    (allowed : Fin (m + 1) → Set P)
    (R : FirstWagonRefinement T hm edge part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩) g)
    (α : UA ↪ P)
    {n : ℕ} (hLen : m + R.extraCuts = n) :
    ∀ j : Fin (R.extraCuts + 1),
      (fineAllowedFromRefinement m R.extraCuts hm α allowed R.permitted
        (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm
          (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen)
            (firstRefinementParent m R.extraCuts hm j)))).Subsingleton := by
  intro j
  have hCancel :
      Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm
        (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen)
          (firstRefinementParent m R.extraCuts hm j)) =
        firstRefinementParent m R.extraCuts hm j := Fin.ext rfl
  rw [hCancel]
  exact (R.canonicalFineAllowed_all_constraints allowed α).1 j

/-- A selected lower stage with its canonical allowed A-part parameters
and genuine selected part-preserving base copies has physical support
girth > q. No free forest, adjacent parameter, hFull or hSingleton
premises remain: all are derived from the actual R and lower stage.

The lower selected ForestTailStage and its base family are still honest
inputs, not manufactured by this theorem; the output picture step and
positive supreme-cycle transfer remain separate obligations.
-/
theorem ForestTailStage.canonicalSelectedLower_coreGirth_from_actualLower
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L VB) (D : RelStructure L P)
    {family : Set (Embedding B D)}
    {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (stage : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (e : Embedding A D)
    (R : FirstWagonRefinement
      (stage.train.restrict
        (sharedOldACarrierInclusion A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding)))
      (by simp : 0 < (q :: tail).length)
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
      stage.system.part (allowed ⟨1, by simp⟩) (q - 1))
    (Large : StructuralRamsey.Partite.System L UA Q)
    {lowerFamily : Set (Embedding
      (stage.system.toRelStructure.induce
        (activeCarrier A stage.system e.toFunctionEmbedding))
      Large.toRelStructure)}
    {lowerTrain : EdgeTrainLevels
      (OldACarrierEdge A
        (stage.system.toRelStructure.induce
          (activeCarrier A stage.system e.toFunctionEmbedding)))
      (List.replicate (R.extraCuts + 1) (q - 1) ++ tail).length}
    (lower : ForestTailStage A
      (stage.system.toRelStructure.induce
        (activeCarrier A stage.system e.toFunctionEmbedding))
      Large.toRelStructure lowerFamily
      (List.replicate (R.extraCuts + 1) (q - 1) ++ tail) lowerTrain
      (fun ρ => Large.part ⁻¹'
        (fineAllowedFromRefinement
          (q :: tail).length R.extraCuts
          (by simp : 0 < (q :: tail).length)
          e.toFunctionEmbedding allowed R.permitted
          (Fin.cast (congrArg (fun k : ℕ => k + 1)
            (canonicalActualLowerHeight q R.extraCuts tail)).symm ρ))))
    (hFamilyParts : ∀ b, b ∈ lowerFamily →
      ∀ x : activeCarrier A stage.system e.toFunctionEmbedding,
        Large.part (b x) =
          activeSourcePart A stage.system e.toFunctionEmbedding x)
    (hq : 2 < q)
    (hMonotone : (q :: tail).Pairwise (· ≤ ·)) :
    GirthGT (supportCopies A
      (lower.system.coarsenVia Large lower.isPartite).toRelStructure) q := by
  let fineAllowed : Fin
      ((List.replicate (R.extraCuts + 1) (q - 1) ++ tail).length + 1) →
      Set UA :=
    fun ρ => fineAllowedFromRefinement
      (q :: tail).length R.extraCuts
      (by simp : 0 < (q :: tail).length)
      e.toFunctionEmbedding allowed R.permitted
      (Fin.cast (congrArg (fun k : ℕ => k + 1)
        (canonicalActualLowerHeight q R.extraCuts tail)).symm ρ)
  have hLen :
      (q :: tail).length + R.extraCuts =
        (List.replicate (R.extraCuts + 1) (q - 1) ++ tail).length :=
    canonicalActualLowerHeight q R.extraCuts tail
  have hSingleton : ∀ j : Fin (R.extraCuts + 1),
      (fineAllowed (Fin.cast
        (congrArg (fun k : ℕ => k + 1) hLen)
        (firstRefinementParent (q :: tail).length R.extraCuts
          (by simp : 0 < (q :: tail).length) j))).Subsingleton := by
    intro j
    exact R.canonicalLowerParent_subsingleton
      allowed e.toFunctionEmbedding hLen j
  exact lower.coarsenedSelected_coreGirth_from_actualLower
    A hA stage.system e.toFunctionEmbedding Large
    fineAllowed hFamilyParts hq hMonotone hSingleton

end StructuralRamsey.Girth.TrainRecursiveWitness

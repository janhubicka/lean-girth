import Girth.TrainRecursiveSelectedCoreGirthFullFromLowerStage
import Girth.TrainRecursiveSelectedLowerActualInputs
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Canonical FirstWagonRefinement discharges the last singleton fine input

The previous real selected-lower-stage girth theorem needs only the
singleton inserted-parent A-parts.  Those singleton constraints are
already part of the genuine older FirstWagonRefinement data:
R.permitted_subsingleton, together with R.permitted_subset.

Choose the actual lower recursive allowed A-parts to be exactly
fineAllowedFromRefinement from R, transported to the literal lower
cutoff-list index by an invertible Fin.cast.  The canonical
FirstWagonRefinement theorem then supplies the missing singleton
condition, with no extra geometry premise.

Consequently a real lower selected ForestTailStage with this canonical
allowed-set choice, selected physical part-preserving gluing family
and monotone q::tail cutoff request has entire physical A-support
girth >q, without separate hFull, hForest, hParameters, hSingleton.

The lower selected stage and actual old refinement remain given. This
does not prove their recursive existence, an output SupremeCycleBound,
or the nontrivial PictureStep. Circulation only.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
universe u v

variable {L : RelLanguage.{u}} {UA VB P Q X : Type v}

private theorem canonicalSelectedLowerLen (q d : ℕ) (tail : List ℕ) :
    (List.replicate (d + 1) (q - 1) ++ tail).length =
      (q :: tail).length + d := by
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain :
  EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}
variable (stage : ForestTailStage A B D family (q :: tail)
  targetTrain allowed)
variable (e : Embedding A D)
local notation "S" =>
  activeCarrier A stage.system e.toFunctionEmbedding

variable (R : FirstWagonRefinement
  (stage.train.restrict
    (sharedOldACarrierInclusion A stage.system.toRelStructure S))
  (by simp : 0 < (q :: tail).length)
  (fun edge => edge.1.1) stage.system.part
  (allowed ⟨1, by simp⟩) (q - 1))

variable (Large : StructuralRamsey.Partite.System L UA Q)
local notation "LowerCuts" =>
  List.replicate (R.extraCuts + 1) (q - 1) ++ tail
local notation "LowerFine" => fun ν : Fin (LowerCuts.length + 1) =>
  fineAllowedFromRefinement
    (q :: tail).length R.extraCuts
    (by simp : 0 < (q :: tail).length)
    e.toFunctionEmbedding allowed R.permitted
    (Fin.cast
      (congrArg (fun k : ℕ => k + 1)
        (canonicalSelectedLowerLen q R.extraCuts tail)) ν)

variable {lowerFamily : Set (Embedding
  (stage.system.toRelStructure.induce S) Large.toRelStructure)}
variable {lowerTrain : EdgeTrainLevels
  (OldACarrierEdge A (stage.system.toRelStructure.induce S))
  LowerCuts.length}
variable (lower : ForestTailStage A
  (stage.system.toRelStructure.induce S) Large.toRelStructure
  lowerFamily LowerCuts lowerTrain
  (fun ν => Large.part ⁻¹' LowerFine ν))
variable (hFamilyParts : ∀ b, b ∈ lowerFamily →
  ∀ x : S, Large.part (b x) =
    activeSourcePart A stage.system e.toFunctionEmbedding x)

include hA hFamilyParts

/-- The true old FirstWagonRefinement and a genuinely constructed
canonical lower selected stage imply the entire coarsened core
support has girth strictly greater than q. No independently assumed
fine parameter, forest, full-system-girth or singleton certificate. -/
theorem ForestTailStage.canonicalSelectedLower_coreGirth
    (hq : 2 < q)
    (hMonotone : (q :: tail).Pairwise (· ≤ ·)) :
    GirthGT
      (supportCopies A
        (lower.system.coarsenVia Large lower.isPartite).toRelStructure) q := by
  have hLen :
      LowerCuts.length = (q :: tail).length + R.extraCuts :=
    canonicalSelectedLowerLen q R.extraCuts tail
  have hConstraints := R.canonicalFineAllowed_all_constraints
    allowed e.toFunctionEmbedding
  have hSingleton : ∀ j : Fin (R.extraCuts + 1),
      (LowerFine
        (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen.symm)
          (firstRefinementParent (q :: tail).length R.extraCuts
            (by simp : 0 < (q :: tail).length) j))).Subsingleton := by
    intro j
    have hCast :
        Fin.cast (congrArg (fun k : ℕ => k + 1) hLen)
          (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen.symm)
            (firstRefinementParent (q :: tail).length R.extraCuts
              (by simp : 0 < (q :: tail).length) j)) =
        firstRefinementParent (q :: tail).length R.extraCuts
          (by simp : 0 < (q :: tail).length) j := by
      apply Fin.ext
      rfl
    change (fineAllowedFromRefinement
      (q :: tail).length R.extraCuts
      (by simp : 0 < (q :: tail).length)
      e.toFunctionEmbedding allowed R.permitted
      (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen)
        (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen.symm)
          (firstRefinementParent (q :: tail).length R.extraCuts
            (by simp : 0 < (q :: tail).length) j)))).Subsingleton
    rw [hCast]
    exact hConstraints.1 j
  exact lower.coarsenedSelected_coreGirth_of_actualLowerTailGirth
    A hA stage.system e.toFunctionEmbedding Large
    LowerFine hFamilyParts hq hMonotone hSingleton

end StructuralRamsey.Girth.TrainRecursiveWitness

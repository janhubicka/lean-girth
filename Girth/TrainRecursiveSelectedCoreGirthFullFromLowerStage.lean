import Girth.TrainRecursiveSelectedCoreGirthFromActualStage
import Girth.TrainRecursiveActualCoarsenedFullRecursiveCutoffs
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Real selected lower stage -> physical core girth, with no fresh fine input

The two independent no-sorry proof interfaces fit together:

1. The actual selected lower ForestTailStage provides the complete
   selected mixed forest, all fine adjacent parameters, and its own
   positive FullSystemGirthGT certificate at each lower cut.
2. Exact selected-gluing physical incidence and the replicated q-1/q
   cutoff index lemma transport the original stage tailGirth to the
   required fine gluing system, not to a synthetic subfamily.

The existing proven first-wagon girth-gain theorem then gives physical
support girth >q for the entire coarsened fine core.

The ONLY residual refinement geometry input here is singleton
allowed A-parts at inserted parents. That is itself already supplied
by the verified FirstWagonRefinement canonicalFineAllowed contract
when the lower recursion uses the prescribed allowed sets.

This theorem remains conditional on a REAL lower selected
ForestTailStage and actual part-preserving base family. It does not
prove this stage exists, attached-output SupremeCycleBound, or the
nontrivial PictureStep. No appendix or manuscript marker promotion.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P V X : Type v}

private theorem selectedCoreLowerHeightEq (q r : ℕ) (tail : List ℕ) :
    (q :: tail).length + r =
      (List.replicate (r + 1) (q - 1) ++ tail).length := by
  simp only [List.length_cons, List.length_append, List.length_replicate]
  omega

variable (A : RelStructure L UA) (hA : A.Irreducible)
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
variable (fineAllowed :
  Fin ((List.replicate (r + 1) (q - 1) ++ tail).length + 1) → Set UA)
variable (S : ForestTailStage A Source D.toRelStructure family
  (List.replicate (r + 1) (q - 1) ++ tail) targetTrain
  (fun ν => D.part ⁻¹' fineAllowed ν))
variable (hFamilyParts : ∀ b, b ∈ family →
  ∀ x : activeCarrier A Old α,
    D.part (b x) = activeSourcePart A Old α x)

local notation "E" => S.system.coarsenVia D S.isPartite

include hFamilyParts

/-- From a literal selected lower recursive stage and the original
monotone q::tail request, infer GirthGT q of the COMPLETE
coarsened physical A-support, without free parameters, mixed forest
or full-system fine-cut assumptions. -/
theorem ForestTailStage.coarsenedSelected_coreGirth_of_actualLowerTailGirth
    (hq : 2 < q)
    (hMonotone : (q :: tail).Pairwise (· ≤ ·))
    (hSingleton : ∀ j : Fin (r + 1),
      (fineAllowed
        (Fin.cast (congrArg (fun k : ℕ => k + 1)
          (selectedCoreLowerHeightEq q r tail))
          (firstRefinementParent (q :: tail).length r
            (by simp : 0 < (q :: tail).length) j))).Subsingleton) :
    GirthGT (supportCopies A E.toRelStructure) q := by
  have hm : 0 < (q :: tail).length := by simp
  have hLen : (q :: tail).length + r =
      (List.replicate (r + 1) (q - 1) ++ tail).length :=
    selectedCoreLowerHeightEq q r tail
  have hHead :
      (List.replicate (r + 1) (q - 1) ++ tail).headD 0 = q - 1 := by
    simp [List.replicate_succ]
  have hBottom :
      q - 1 ≤ (List.replicate (r + 1) (q - 1) ++ tail).headD 0 := by
    omega
  have hFull :
      ∀ ν : Fin ((q :: tail).length + r + 1),
        0 < ν.val → ν.val < (q :: tail).length + r →
        (activeGluingWitnessOrderOneData A Old α E.toRelStructure
          (fun i : {b : DesignatedCopy Source D.toRelStructure
              S.system family // b ∈ S.selected} =>
            (selectedPartiteGluingFamily_of_largeBase
              Target D S.system S.isPartite family hFamilyParts
              S.selected i).toEmbedding)
          (S.train.castHeight hLen.symm) ν).FullSystemGirthGT
            (if ν.val ≤ r then q - 1 else q) := by
    intro ν hPos hInterior
    exact S.coarsenedSelected_fullSystem_for_attachmentHeight
      A Old α D hFamilyParts hLen rfl hMonotone ν hPos hInterior
  exact S.coarsenedSelected_coreGirth_of_actualStage
    A hA Old α D fineAllowed hFamilyParts hm hq hLen
    hBottom hSingleton hFull

end StructuralRamsey.Girth.TrainRecursiveWitness

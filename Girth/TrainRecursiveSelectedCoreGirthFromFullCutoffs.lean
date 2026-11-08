import Girth.TrainRecursiveActualCoarsenedFullRecursiveCutoffs
import Girth.TrainRecursiveFineWitnessBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Nontrivial fine selected lower stage gives core A-support girth q

The local q>2 attachment needs ordinary support girth of the selected
coarsened fine witness. Previously the geometric girth-gain constructor
takes a separately postulated indexed FullSystemGirthGT at EVERY
positive proper fine cut. For the genuine selected lower ForestTailStage
this entire positive-bound family follows instead from its own tailGirth:
the coarsened selected incidence is identical to the original selected
picture, and the exact q-1/q numeric threshold follows from the lower
recursive cutoff vector and the original monotone q::tail request.

This proof removes hFull from the local core-girth interface, without
deleting ambient physical support edges or identifying selected labels
with equal carriers. It still requires the real selected lower stage,
part preserving gluing family, physical mixed forest, adjacent parameters
and singleton first-refinement parts. It does NOT create the recursive
lower witness, prove the actual output SupremeCycleBound, or establish
the final nontrivial PictureStep. No appendix or TeX markers.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
universe u v

variable {L : RelLanguage.{u}} {UA P V X : Type v}
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
variable {targetTrain : EdgeTrainLevels
  (OldACarrierEdge A Source)
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
  selectedPartiteGluingFamily_of_largeBase
    Target D S.system S.isPartite family hFamilyParts
    S.selected i

/-- Exact arithmetic of the refined fine-train height; independent
of the selected lower witness. -/
private theorem selectedFineHeightEq {q r : ℕ} {tail : List ℕ} :
    (q :: tail).length + r =
      (List.replicate (r + 1) (q - 1) ++ tail).length := by
  simp only [List.length_cons, List.length_append, List.length_replicate]
  omega

include hFamilyParts

/-- In the true recursive selected fine witness, the indexed
full-system gluing bounds at q-1/q are DERIVED from the lower selected
stage rather than stipulated. Thus the existing finite-first-wagon
girth-gain theorem yields the genuine A-support girth >q of the
complete coarsened lower core. -/
theorem ForestTailStage.coarsenedSelected_coreGirth_of_lowerFineStage
    (hq : 2 < q)
    (hMonotone : (q :: tail).Pairwise (· ≤ ·))
    (fineAllowed : Fin ((q :: tail).length + r + 1) → Set UA)
    (hParameters :
      (S.train.castHeight
        (selectedFineHeightEq (q := q) (r := r) (tail := tail)).symm).AdjacentParameters
        (fun edge => edge.1) (fun ν => E.part ⁻¹' fineAllowed ν))
    (hSingleton : ∀ j : Fin (r + 1),
      (fineAllowed (firstRefinementParent (q :: tail).length r
        (by simp : 0 < (q :: tail).length) j)).Subsingleton)
    (hForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A (fun i : Selected => (Gluing i).toEmbedding))
      (q - 1)) :
    GirthGT (supportCopies A E.toRelStructure) q := by
  have hLen : (q :: tail).length + r =
      (List.replicate (r + 1) (q - 1) ++ tail).length :=
    selectedFineHeightEq (q := q) (r := r) (tail := tail)
  let T := S.train.castHeight hLen.symm
  have hParams :
      T.AdjacentParameters (fun edge => edge.1)
        (fun ν => E.part ⁻¹' fineAllowed ν) := by
    exact hParameters
  have hFull : ∀ ν : Fin ((q :: tail).length + r + 1),
      0 < ν.val → ν.val < (q :: tail).length + r →
      (activeGluingWitnessOrderOneData A Old α E.toRelStructure
        (fun i : Selected => (Gluing i).toEmbedding) T ν).FullSystemGirthGT
          (if ν.val ≤ r then q - 1 else q) := by
    intro ν hPos hInterior
    exact S.coarsenedSelected_fullSystem_for_attachmentHeight
      A Old α D hFamilyParts hLen rfl hMonotone ν hPos hInterior
  exact activeFineWitness_supportGirth
    (m := (q :: tail).length) (d := r) (q := q)
    A hA Old α E Gluing
    (by simp : 0 < (q :: tail).length) hq
    T fineAllowed hParams hSingleton hForest hFull

end StructuralRamsey.Girth.TrainRecursiveWitness

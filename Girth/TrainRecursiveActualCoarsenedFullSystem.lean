import Girth.TrainRecursiveCoarsenedExactIncidenceAudit
import Girth.TrainRecursiveCoarsenedSelectedFullSystem
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Literal selected coarsened full system bound from audited incidence equality

This proof uses the separately audited complete physical incidence
equality, not an implicit coercion of two different gluing families.
The canonical selected gluing index type is exactly the subtype of
selected designated-copy labels and its physical source map is exact.
At every positive lower stage cut the original ForestTailStage tail
certificate therefore transfers with all legal supreme plans.

The monotone version preserves the same original labels, all ambient
physical A-support edges, wagon classes, and full global system girth.
The genuine lower selected stage and part-preserving family remain
real construction inputs. No geometric local PictureStep, no output
supreme-cycle bound and no artificial girth of a partite power.
Circulation only; no appendix or TeX validation-mark promotion.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
universe u v

variable {L : RelLanguage.{u}} {UA P V X : Type v}
variable (A : RelStructure L UA)
variable (Old : StructuralRamsey.Partite.System L P X)
variable (α : UA ↪ P)
variable (D : StructuralRamsey.Partite.System L UA V)
local notation "Source" =>
  Old.toRelStructure.induce (activeCarrier A Old α)
local notation "Target" =>
  actualActiveSubsystemPartite A Old α

variable {family : Set (Embedding Source D.toRelStructure)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A Source) t.length}
variable {allowed : Fin (t.length + 1) → Set V}
variable (S : ForestTailStage A Source D.toRelStructure family t targetTrain allowed)
variable (hFamilyParts : ∀ b, b ∈ family →
  ∀ x : activeCarrier A Old α,
    D.part (b x) = activeSourcePart A Old α x)

local notation "Selected" =>
  {b : DesignatedCopy Source D.toRelStructure S.system family //
    b ∈ S.selected}
local notation "Gluing" => fun i : Selected =>
  (selectedPartiteGluingFamily_of_largeBase
    Target D S.system S.isPartite family hFamilyParts
    S.selected i).toEmbedding

include hFamilyParts

/-- EXACT complete global selected-gluing system girth at every positive
proper lower cut, directly from S.tailGirth and equality of complete
original selected-copy incidence with coarsened physical incidence. -/
theorem ForestTailStage.coarsenedSelected_fullSystem_at_positive
    (j : Fin t.length) (hj : 0 < j.val) :
    (activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      Gluing S.train j.castSucc).FullSystemGirthGT (t.get j) := by
  apply (S.coarsenedSelected_fullSystem_iff_original
    A Old α D hFamilyParts j.castSucc (t.get j)).mpr
  exact S.tailGirth j hj

/-- A smaller numeric full-system cutoff holds for the SAME physical
gluing record, without deleting edges or changing selected indices. -/
theorem ForestTailStage.coarsenedSelected_fullSystem_at_positive_mono
    (j : Fin t.length) (hj : 0 < j.val)
    (q : ℕ) (hq : q ≤ t.get j) :
    (activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      Gluing S.train j.castSucc).FullSystemGirthGT q := by
  have hFull :
      (activeGluingWitnessOrderOneData A Old α
        (S.system.coarsenVia D S.isPartite).toRelStructure
        Gluing S.train j.castSucc).FullSystemGirthGT (t.get j) :=
    S.coarsenedSelected_fullSystem_at_positive
      A Old α D hFamilyParts j hj
  refine ⟨hFull.1, ?_⟩
  intro n K hAccept hOrder
  exact hFull.2 n K hAccept (by omega)

end StructuralRamsey.Girth.TrainRecursiveWitness

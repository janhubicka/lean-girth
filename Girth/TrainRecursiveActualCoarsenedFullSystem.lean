import Girth.TrainRecursiveCoarsenedSelectedFullSystem
import Girth.ActualActivePartitePresentation
import Girth.TrainRecursiveLargeBaseCoarsening
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Positive FullSystemGirthGT for the LITERAL coarsened selected gluing family

The larger-base lower recursion uses the entire true active source
over an A-partite base D, and selects a genuine set of target copies.
Every selected copy's base map must preserve A-parts to become an
actual gluing map after coarsening S.system via D.part.

The generic checked selectedGluing_fullSystem_at_positive asks for
an honest equivalence between the gluing-family index type and the
literal selected designated-copy subtype, plus equality of every
physical carrier. For the canonical selected partite gluing family
these two inputs are now DERIVED, not supplied:

* the index type IS the selected designated-copy subtype, hence the
  equivalence is Equiv.refl;
* toCoarsenedPartiteEmbedding.toEmbedding is definitionally the
  original designated copy's literal relational embedding, so
  their full physical A-carriers are equal.

Therefore every positive lower-stage selected-picture full-system
certificate gives the complete positive gluing FullSystemGirthGT,
including legal simultaneous replacement plans. The numerical
cutoff can be lowered without removing any ambient physical edge
or merging two apparently equal carrier labels.

This is conditional on the REAL lower ForestTailStage and the actual
part-preserving selected base family. It does not construct that
stage, justify first-retained target-cut girth, or prove the attached
output SupremeCycleBound. Circulation only; no appendix.
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

include hFamilyParts

/-- The coarsened selected gluing family indexed by the literal lower
stage selected subtype has FULL system girth at every positive cut,
with the exact genuine physical gluing embeddings and wagon labels. -/
theorem ForestTailStage.coarsenedSelected_fullSystem_at_positive
    (j : Fin t.length) (hj : 0 < j.val) :
    (activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      (fun i : {b : DesignatedCopy Source D.toRelStructure S.system family //
          b ∈ S.selected} =>
        (selectedPartiteGluingFamily_of_largeBase
          Target D S.system S.isPartite family hFamilyParts
          S.selected i).toEmbedding)
      S.train j.castSucc).FullSystemGirthGT (t.get j) := by
  -- Directly specialize the checked selected-gluing equivalence. The
  -- coarsened system has definitionally the same relational reduct, and
  -- the selected partite embedding has the same underlying map.
  exact S.selectedGluing_fullSystem_at_positive
    A Old α D.toRelStructure
    (fun i : {b : DesignatedCopy Source D.toRelStructure S.system family //
        b ∈ S.selected} =>
      (selectedPartiteGluingFamily_of_largeBase
        Target D S.system S.isPartite family hFamilyParts
        S.selected i).toEmbedding)
    (Equiv.refl _)
    (by intro i; rfl) j hj

/-- The same canonical actual positive selected gluing certificate
at any smaller cutoff, with no loss of labels, support or plans. -/
theorem ForestTailStage.coarsenedSelected_fullSystem_at_positive_mono
    (j : Fin t.length) (hj : 0 < j.val)
    (q : ℕ) (hq : q ≤ t.get j) :
    (activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      (fun i : {b : DesignatedCopy Source D.toRelStructure S.system family //
          b ∈ S.selected} =>
        (selectedPartiteGluingFamily_of_largeBase
          Target D S.system S.isPartite family hFamilyParts
          S.selected i).toEmbedding)
      S.train j.castSucc).FullSystemGirthGT q := by
  have hFull := S.coarsenedSelected_fullSystem_at_positive
    A Old α D hFamilyParts j hj
  refine ⟨hFull.1, ?_⟩
  intro n K hAccept hOrder
  exact hFull.2 n K hAccept (by omega)

end StructuralRamsey.Girth.TrainRecursiveWitness

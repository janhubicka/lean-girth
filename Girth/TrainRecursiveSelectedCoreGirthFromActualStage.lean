import Girth.TrainRecursiveCanonicalFineParametersCast
import Girth.TrainRecursiveSelectedWitnessConsequences
import Girth.TrainRecursiveFineWitnessBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Genuine selected lower stage supplies both fine-parameter and mixed-forest inputs

The local q>2 core-girth gain needs an indexed complete gluing
FullSystemGirthGT family, singleton inserted-parent fine parts, fine
adjacent parameters, and a mixed forest of selected copies.

For the ACTUAL selected lower ForestTailStage over its true active
source, the last two data are already part of the constructed stage:
* coarsening the lower large-base part map and casting its train height
  supplies all fine adjacent parameters, provided the lower allowed
  sets are the literal preimages of the fine permitted A-part sets;
* the complete selected bottom mixed forest restricts to the literal
  selected gluing subtype, preserving ALL ambient physical A-edges.

This theorem consequently has NO independent hParameters or hForest.
The genuine full-system cut certificates and singleton fine-part
constraints remain explicit inputs; the companion q-1/q reduction
derives the former from actual lower tailGirth when available.

No invented lower stage, no selected-label quotient, no support
pruning, no assumed output SupremeCycleBound. Circulation only.
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

variable {t : List ℕ}
variable {family : Set (Embedding Source D.toRelStructure)}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A Source) t.length}
variable (fineAllowed : Fin (t.length + 1) → Set UA)
variable (S : ForestTailStage A Source D.toRelStructure family t targetTrain
  (fun ν => D.part ⁻¹' fineAllowed ν))
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

include hFamilyParts

/-- Physical support girth of the canonical coarsened lower stage
follows from its ORIGINAL selected bottom mixed forest, actual train
adjacent parameters and an explicit full-system fine cut family.
No external hForest or hParameters assumptions are used. -/
theorem ForestTailStage.coarsenedSelected_coreGirth_of_actualStage
    {m d q : ℕ} (hm : 0 < m) (hq : 2 < q)
    (hLen : m + d = t.length)
    (hBottom : q - 1 ≤ t.headD 0)
    (hSingleton : ∀ j : Fin (d + 1),
      (fineAllowed
        (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen)
          (firstRefinementParent m d hm j))).Subsingleton)
    (hFull : ∀ ν : Fin (m + d + 1), 0 < ν.val →
      ν.val < m + d →
      (activeGluingWitnessOrderOneData A Old α E.toRelStructure
        (fun i : Selected => (Gluing i).toEmbedding)
        (S.train.castHeight hLen.symm) ν).FullSystemGirthGT
          (if ν.val ≤ d then q - 1 else q)) :
    GirthGT (supportCopies A E.toRelStructure) q := by
  let actualFineAllowed : Fin (m + d + 1) → Set UA :=
    fun ν => fineAllowed
      (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen) ν)
  have hParameters :
      (S.train.castHeight hLen.symm).AdjacentParameters
        (fun edge => edge.1)
        (fun ν => E.part ⁻¹' actualFineAllowed ν) :=
    S.coarsened_adjacentParameters_castHeight_preimage
      A Source D fineAllowed hLen
  have hForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A
        (fun i : Selected => (Gluing i).toEmbedding)) (q - 1) := by
    apply S.selectedEmbeddings_mixedForest
      (fun i : Selected => (Gluing i).toEmbedding)
      ?_ (q - 1) hBottom
    intro i
    exact ⟨i.1, i.2, rfl⟩
  exact activeFineWitness_supportGirth
    A hA Old α E Gluing hm hq
    (S.train.castHeight hLen.symm) actualFineAllowed
    hParameters hSingleton hForest hFull

end StructuralRamsey.Girth.TrainRecursiveWitness

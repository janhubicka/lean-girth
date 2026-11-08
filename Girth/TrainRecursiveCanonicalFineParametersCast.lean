import Girth.TrainRecursiveCoarsenedStageParameters
import Girth.TrainRecursiveExactHeightTransport
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Coarsened genuine selected-stage parameters through the exact height equality

For a real lower ForestTailStage whose large-base allowed sets are the
inverse images of the prescribed fine A-part sets, adjacent parameters
of the WHOLE physical train follow from the stage's own parameters.
Coarsening the part map retains every edge and wagon class. Transporting
the exact same train along an equality of heights changes only the
index type of levels; it cannot introduce a missing local witness.

This removes an independently stated hParameters assumption from
the canonical fine witness; it does NOT establish singleton parent
constraints, active local Ramsey steps, or global output girth.

The transport is stated for an arbitrary genuine lower selected stage;
it does not assume that the current source is a larger union of A-parts.
Circulation only; no appendix or TeX markers.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

theorem ForestTailStage.coarsened_adjacentParameters_castHeight_preimage
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : StructuralRamsey.Partite.System L UA P)
    {family : Set (Embedding B D.toRelStructure)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (S : ForestTailStage A B D.toRelStructure family t targetTrain
      (fun ν => D.part ⁻¹' fineAllowed ν))
    {m : ℕ} (hLen : m = t.length) :
    (S.train.castHeight hLen.symm).AdjacentParameters
      (fun edge => edge.1)
      (fun ν : Fin (m + 1) =>
        (S.system.coarsenVia D S.isPartite).part ⁻¹'
          fineAllowed
            (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen) ν)) := by
  have hOriginal :
      S.train.AdjacentParameters (fun edge => edge.1)
        (fun ν => (S.system.coarsenVia D S.isPartite).part ⁻¹'
          fineAllowed ν) :=
    S.coarsened_adjacentParameters_preimage A B D fineAllowed
  exact S.train.castHeight_adjacentParameters
    (fun edge => edge.1) hLen.symm
    (fun ν => (S.system.coarsenVia D S.isPartite).part ⁻¹'
      fineAllowed ν) hOriginal

end StructuralRamsey.Girth.TrainRecursiveWitness

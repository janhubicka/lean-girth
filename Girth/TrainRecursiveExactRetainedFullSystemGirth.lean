import Girth.TrainRecursiveFineWitnessSystemGirth
import Girth.TrainRecursiveRefinementForget

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact FULL system-girth at retained first-wagon cutoffs

The previously checked transfer
activeGluingWitness_interiorFull_of_fine only exports girth >2,
despite the retained fine gluing record being literally the SAME
OrderOneData at its corresponding fine level.

The original recursive tail request may have cutoff t[j] much
GREATER than the current head q.  Replacing it by a uniform q-bound
is insufficient for the positive attached SupremeCycleBound in
the next step.  Keep the exact requested cutoff parameter rather
than lowering it to two or q.

The forgetFirstCuts relation at every old level μ is defined to be
the original fine relation at firstForgetIndex m d μ, with identical
physical edges, designated gluing embeddings and quotient wagons.
Thus the FULL global simultaneous supreme-cycle certificate transfers
at precisely its original cutoff, not merely ordinary edge girth.

No selected-copy index quotient, edge pruning, unproved output girth,
or new full-system assumption.  This is a conversion of an ALREADY
GIVEN genuine fine full-system certificate.  Circulation only.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X Y I : Type v}

/-- Exact full-system-girth threshold through one original retained
cut. Unlike the older >2 specialization this preserves ALL requested
positive-tail thresholds (and the entire original incidence system). -/
theorem activeGluingWitness_retainedFullSystem_of_fine
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P) (R : RelStructure L Y)
    (f : I → Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m d : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A R) (m + d))
    (hm : 0 < m)
    (μ : Fin (m + 1)) (q : ℕ)
    (hFine :
      (activeGluingWitnessOrderOneData A C α R f T
        (EdgeTrainLevels.firstForgetIndex m d μ)).FullSystemGirthGT q) :
    (activeGluingWitnessOrderOneData A C α R f
      (T.forgetFirstCuts hm) μ).FullSystemGirthGT q := by
  change (activeGluingWitnessOrderOneData A C α R f T
    (EdgeTrainLevels.firstForgetIndex m d μ)).FullSystemGirthGT q
  exact hFine

/-- Simultaneously preserve the EXACT original cutoff at each proper
positive retained cut. This is the form needed for a lower selected
tail vector whose entries are not necessarily constant. -/
theorem activeGluingWitness_retainedFullSystem_all_tail
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P) (R : RelStructure L Y)
    (f : I → Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m d : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A R) (m + d))
    (hm : 0 < m)
    (cutoff : Fin (m + 1) → ℕ)
    (hFine : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      (activeGluingWitnessOrderOneData A C α R f T
        (EdgeTrainLevels.firstForgetIndex m d μ)).FullSystemGirthGT
          (cutoff μ)) :
    ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      (activeGluingWitnessOrderOneData A C α R f
        (T.forgetFirstCuts hm) μ).FullSystemGirthGT (cutoff μ) := by
  intro μ hPos hInterior
  exact activeGluingWitness_retainedFullSystem_of_fine
    A C α R f T hm μ (cutoff μ) (hFine μ hPos hInterior)

end StructuralRamsey.Girth

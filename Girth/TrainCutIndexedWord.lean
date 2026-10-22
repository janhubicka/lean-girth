import Girth.TrainCyclicRestriction
import Girth.TrainCyclicRunWrap

/-!
# A typed word on the actual cyclic owner cuts

The maximal owner-cut enumeration is now connected directly to
BigCycle.restrictConnectorWord. Consecutive owner labels at cuts are
automatically different, including across wraparound; the output
connectors are proved distinct from the original source's connectors.
The only missing geometric inputs are the target connectors and their
two physical incidences, together with their exact source images.

This is the actual indexed syntax, not the still-open instantiation
of A2/A3 from the selected picture's physical gluing quotient.
-/

namespace StructuralRamsey.Girth

universe u v w

/-- Successive pre-cut owner labels differ even across the cyclic wrap. -/
theorem cyclicOwner_at_consecutive_cuts_ne
    {Owner : Type u} {n : ℕ} (owner : Fin n → Owner)
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (j : Fin (cyclicOwnerChanges owner)) :
    owner (cyclicOwnerCutIndex owner j) ≠
      owner (cyclicOwnerCutIndex owner (cyclicSucc j)) := by
  have h := cyclicOwnerRunLabel_adjacent_ne owner (trainCyclicPred j)
  rw [cyclicOwnerRunLabel_eq_next_cut owner (trainCyclicPred j),
    cyclicSucc_trainCyclicPred_of_two_le hCuts,
    cyclicOwnerRunLabel_eq_next_cut owner j] at h
  exact h

namespace OrderOneData

variable {V E I P : Type v} {V' E' I' P' : Type w}
variable {Owner : Type u}
variable {D : OrderOneData V E I P} {D' : OrderOneData V' E' I' P'}
variable {n : ℕ}

/-- A genuine typed cut-indexed word from the input cycle. No
target connector injectivity or adjacent-label inequality is assumed:
the two are established by the source big cycle and cut indexing. -/
noncomputable def cutIndexedWord
    (C : D.BigCycle n) (owner : Fin n → Owner)
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (labelOf : Owner → I' ⊕ E') (hLabel : Function.Injective labelOf)
    (vertex : V' → V) (wagon : P' → P)
    (connector : Fin (cyclicOwnerChanges owner) → V' ⊕ P')
    (hConnector : ∀ j : Fin (cyclicOwnerChanges owner),
      C.connector (cyclicOwnerCutIndex owner j) =
        Sum.map vertex wagon (connector j))
    (hLeft : ∀ j : Fin (cyclicOwnerChanges owner),
      D'.Incident (labelOf (owner (cyclicOwnerCutIndex owner j)))
        (connector j))
    (hRight : ∀ j : Fin (cyclicOwnerChanges owner),
      D'.Incident
        (labelOf (owner (cyclicOwnerCutIndex owner (cyclicSucc j))))
        (connector j)) :
    D'.BigCycle (cyclicOwnerChanges owner) :=
  C.restrictConnectorWord (D' := D') hCuts (cyclicOwnerCutIndex owner)
    vertex wagon
    (fun j => labelOf (owner (cyclicOwnerCutIndex owner j)))
    connector hConnector
    (by
      intro j h
      exact cyclicOwner_at_consecutive_cuts_ne owner hCuts j (hLabel h))
    hLeft hRight

end OrderOneData
end StructuralRamsey.Girth

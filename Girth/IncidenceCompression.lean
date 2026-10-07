import Girth.IncidenceCircuit
import Girth.CyclicRun

/-! # Compressing cyclic incidence runs

Before the final incidence contradiction, the circulation proof has one label
for every edge of the original Berge cycle.  Consecutive labels may agree.
This file formalizes the elementary cyclic compression which removes such
redundant transitions while preserving the connector incidences.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- Cyclic incidence data before maximal equal-label runs have been
compressed.  The label word is required to be nonconstant. -/
structure RawCyclicIncidenceData (edge : E → Set W) where
  length : ℕ
  hlength : 2 ≤ length
  label : Fin length → E
  connector : Fin length → W
  connector_injective : Function.Injective connector
  left_mem : ∀ i, connector i ∈ edge (label i)
  right_mem : ∀ i, connector i ∈ edge (label (cyclicSucc i))
  nonconstant : ∃ i j, label i ≠ label j

namespace RawCyclicIncidenceData

variable {edge : E → Set W}

/-- Cyclic translation commutes with cyclic successor. -/
theorem finCycle_cyclicSucc
    {n : ℕ} (i s : Fin n) :
    finCycle (cyclicSucc i) s =
      cyclicSucc (finCycle i s) := by
  rw [cyclicSucc_eq_finRotate, cyclicSucc_eq_finRotate]
  simp only [finRotate_apply, finCycle_apply]
  ac_rfl

/-- Rotate the cyclic indexing without changing any incidence data. -/
def rotate
    (d : RawCyclicIncidenceData edge)
    (s : Fin d.length) :
    RawCyclicIncidenceData edge where
  length := d.length
  hlength := d.hlength
  label i := d.label (finCycle i s)
  connector i := d.connector (finCycle i s)
  connector_injective := by
    intro i j hij
    apply (finCycle s).injective
    exact d.connector_injective hij
  left_mem i := d.left_mem (finCycle i s)
  right_mem i := by
    have h := d.right_mem (finCycle i s)
    rw [← finCycle_cyclicSucc i s] at h
    exact h
  nonconstant := by
    rcases d.nonconstant with ⟨i, j, hij⟩
    let i' : Fin d.length := (finCycle s).symm i
    let j' : Fin d.length := (finCycle s).symm j
    refine ⟨i', j', ?_⟩
    simpa [i', j'] using hij

/-- Canonical last index of nonempty raw cyclic data. -/
def last
    (d : RawCyclicIncidenceData edge) :
    Fin d.length :=
  ⟨d.length - 1, by omega⟩

/-- Rotating to the successor of an index sends the last new position back to
that index. -/
theorem finCycle_last_cyclicSucc
    (d : RawCyclicIncidenceData edge)
    (i : Fin d.length) :
    finCycle d.last (cyclicSucc i) = i := by
  haveI : NeZero d.length := ⟨by omega⟩
  rw [finCycle_apply, cyclicSucc_eq_finRotate, finRotate_apply]
  apply Fin.ext
  simp [RawCyclicIncidenceData.last, Fin.add_def]
  have hi : i.1 < d.length := i.2
  omega

/-- If the transition at i is redundant, rotate it to the wrap-around:
the last and first labels of the rotated word agree. -/
theorem rotate_succ_last_label_eq_zero
    (d : RawCyclicIncidenceData edge)
    (i : Fin d.length)
    (heq : d.label i = d.label (cyclicSucc i)) :
    (d.rotate (cyclicSucc i)).label
        (d.rotate (cyclicSucc i)).last =
      (d.rotate (cyclicSucc i)).label 0 := by
  change
    d.label (finCycle d.last (cyclicSucc i)) =
      d.label (finCycle 0 (cyclicSucc i))
  rw [d.finCycle_last_cyclicSucc i]
  simpa [finCycle_apply] using heq

end RawCyclicIncidenceData

end StructuralRamsey.Girth

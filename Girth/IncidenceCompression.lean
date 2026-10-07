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
  have hlast : d.last = (-1 : Fin d.length) := by
    apply Fin.ext
    change d.length - 1 = ((-1 : Fin d.length) : ℕ)
    conv_rhs =>
      rw [show d.length = (d.length - 1) + 1 by omega]
    rw [Fin.coe_neg_one]
  rw [finCycle_apply, cyclicSucc_eq_finRotate, finRotate_apply, hlast]
  calc
    (-1 : Fin d.length) + (i + 1) =
        ((-1 : Fin d.length) + 1) + i := by ac_rfl
    _ = i := by simp

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


/-- Inclusion of all indices except the last one. -/
def keepBeforeLast
    (d : RawCyclicIncidenceData edge)
    (i : Fin (d.length - 1)) :
    Fin d.length :=
  ⟨i.1, by omega⟩

theorem keepBeforeLast_injective
    (d : RawCyclicIncidenceData edge) :
    Function.Injective d.keepBeforeLast := by
  intro i j hij
  apply Fin.ext
  exact congrArg Fin.val hij

/-- If the last and first labels agree, delete the redundant last label and
last connector.  Nonconstancy guarantees this operation is only used when at
least three positions remain. -/
def dropLast
    (d : RawCyclicIncidenceData edge)
    (h3 : 3 ≤ d.length)
    (hwrap : d.label d.last = d.label 0) :
    RawCyclicIncidenceData edge := by
  classical
  let keep := d.keepBeforeLast
  refine
    { length := d.length - 1
      hlength := by omega
      label := fun i => d.label (keep i)
      connector := fun i => d.connector (keep i)
      connector_injective := ?_
      left_mem := ?_
      right_mem := ?_
      nonconstant := ?_ }
  · intro i j hij
    apply d.keepBeforeLast_injective
    exact d.connector_injective hij
  · intro i
    exact d.left_mem (keep i)
  · intro i
    let oi : Fin d.length := keep i
    by_cases hnext : i.1 + 1 < d.length - 1
    · let j : Fin (d.length - 1) := ⟨i.1 + 1, hnext⟩
      have hsuccNew : cyclicSucc i = j := by
        apply Fin.ext
        change (i.1 + 1) % (d.length - 1) = i.1 + 1
        rw [Nat.mod_eq_of_lt hnext]
      have hsuccOld : cyclicSucc oi = keep j := by
        apply Fin.ext
        change (i.1 + 1) % d.length = j.1
        dsimp [j]
        rw [Nat.mod_eq_of_lt (by omega)]
      have h := d.right_mem oi
      rw [hsuccOld] at h
      simpa [hsuccNew, oi] using h
    · have hilast : i.1 + 1 = d.length - 1 := by
        omega
      have hsuccNew :
          cyclicSucc i = (0 : Fin (d.length - 1)) := by
        apply Fin.ext
        change (i.1 + 1) % (d.length - 1) = 0
        rw [hilast, Nat.mod_self]
      have hsuccOld : cyclicSucc oi = d.last := by
        apply Fin.ext
        change (i.1 + 1) % d.length = d.length - 1
        rw [hilast, Nat.mod_eq_of_lt (by omega)]
      have h := d.right_mem oi
      rw [hsuccOld, hwrap] at h
      simpa [hsuccNew, oi, keep, keepBeforeLast] using h
  · by_contra hconst
    push_neg at hconst
    have hAll : ∀ i : Fin d.length, d.label i = d.label 0 := by
      intro i
      by_cases hi : i = d.last
      · subst i
        exact hwrap
      · have hvalne : i.1 ≠ d.length - 1 := by
          intro hval
          apply hi
          apply Fin.ext
          simpa [RawCyclicIncidenceData.last] using hval
        have hlt : i.1 < d.length - 1 := by
          omega
        let i' : Fin (d.length - 1) := ⟨i.1, hlt⟩
        have hEq :=
          hconst i' (0 : Fin (d.length - 1))
        change
          d.label (keep i') =
            d.label (keep (0 : Fin (d.length - 1))) at hEq
        simpa [i', keep, keepBeforeLast] using hEq
    rcases d.nonconstant with ⟨i, j, hij⟩
    exact hij ((hAll i).trans (hAll j).symm)

/-- Dropping the redundant wrap-around strictly decreases the length. -/
theorem dropLast_length_lt
    (d : RawCyclicIncidenceData edge)
    (h3 : 3 ≤ d.length)
    (hwrap : d.label d.last = d.label 0) :
    (d.dropLast h3 hwrap).length < d.length := by
  dsimp [dropLast]
  omega

end RawCyclicIncidenceData

end StructuralRamsey.Girth

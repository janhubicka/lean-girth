import Girth.TrainCheckedCycleWord
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Genuine simultaneous supreme at source length two from a single short

The global BigCycle legality clause is essential in general:
simultaneous locally legal replacements may collide. At n=2 there is
only ONE non-supreme occurrence. A chosen ShortValid physical edge
therefore supplies a literal legal two-occurrence output word, with
the same two distinct connectors, original supreme designated label,
and the chosen real short edge label. This is a FULL simultaneous
supreme certificate, not merely the weaker local piece condition.

Both orientations, including the cyclic wrap, are encoded directly.
No A1/A2/A3 assumption, fake source B-label, wagon identification,
or lower witness is smuggled into the proof. A later bridge theorem
may use this to discharge order-one exactly-two-cut output cycles.
-/

namespace StructuralRamsey.Girth

universe v
variable {V E I P : Type v}

namespace OrderOneData

variable (D : OrderOneData V E I P)

/-- At n=2 a genuine short replacing occurrence one makes a complete
globally valid two-letter replacement word. -/
theorem BigCycle.two_short_at_zero_simultaneous
    (C : D.BigCycle 2)
    (hk : D.designated (C.label 0))
    (e : E)
    (hShort : C.ShortValid D 0 1 e) :
    C.HasSimultaneousSupreme := by
  classical
  have hSucc0 : cyclicSucc (0 : Fin 2) = 1 := by decide
  have hSucc1 : cyclicSucc (1 : Fin 2) = 0 := by decide
  have hPred1 : trainCyclicPred (1 : Fin 2) = 0 := by decide
  have hDifferent : C.label (0 : Fin 2) ≠ C.label 1 := by
    simpa only [hSucc0] using C.adjacent_ne 0
  have hPhysical : C.label (0 : Fin 2) ≠ Sum.inr e := by
    intro h
    have hBad : D.designated (Sum.inr e) := by
      simpa only [h] using hk
    exact hBad
  let pieces : Fin 2 → TrainSupremePiece E P := ![.keep, .short e]
  have hValid : C.PlanValid D 0 pieces := by
    intro j
    fin_cases j
    · constructor
      · intro _; rfl
      · intro h; exact (h rfl).elim
    · constructor
      · intro h; exact (hDifferent h.symm).elim
      · intro _; exact hShort
  let B : D.BigCycle 2 := {
    length_ge_two := by decide
    label := ![C.label 0, Sum.inr e]
    connector := C.connector
    adjacent_ne := by
      intro i
      fin_cases i
      · simpa [cyclicSucc] using hPhysical
      · simpa [cyclicSucc] using hPhysical.symm
    connector_injective := C.connector_injective
    left_incident := by
      intro i
      fin_cases i
      · simpa using C.left_incident 0
      · exact hShort.2.2
    right_incident := by
      intro i
      fin_cases i
      · simpa only [hPred1] using hShort.2.1
      · simpa [cyclicSucc] using C.right_incident 1
  }
  have hWord : List.ofFn (fun i : Fin 2 => (B.label i, B.connector i)) =
      C.resultWord D pieces := by
    rfl
  exact ⟨0, hk, pieces, hValid, 2, B, hWord⟩

/-- The second orientation is symmetric but kept literal to check
the wrap boundary and actual selected source occurrence. -/
theorem BigCycle.two_short_at_one_simultaneous
    (C : D.BigCycle 2)
    (hk : D.designated (C.label 1))
    (e : E)
    (hShort : C.ShortValid D 1 0 e) :
    C.HasSimultaneousSupreme := by
  classical
  have hSucc0 : cyclicSucc (0 : Fin 2) = 1 := by decide
  have hSucc1 : cyclicSucc (1 : Fin 2) = 0 := by decide
  have hPred0 : trainCyclicPred (0 : Fin 2) = 1 := by decide
  have hDifferent : C.label (0 : Fin 2) ≠ C.label 1 := by
    simpa only [hSucc0] using C.adjacent_ne 0
  have hPhysical : C.label (1 : Fin 2) ≠ Sum.inr e := by
    intro h
    have hBad : D.designated (Sum.inr e) := by
      simpa only [h] using hk
    exact hBad
  let pieces : Fin 2 → TrainSupremePiece E P := ![.short e, .keep]
  have hValid : C.PlanValid D 1 pieces := by
    intro j
    fin_cases j
    · constructor
      · intro h; exact (hDifferent h).elim
      · intro _; exact hShort
    · constructor
      · intro _; rfl
      · intro h; exact (h rfl).elim
  let B : D.BigCycle 2 := {
    length_ge_two := by decide
    label := ![Sum.inr e, C.label 1]
    connector := C.connector
    adjacent_ne := by
      intro i
      fin_cases i
      · simpa [cyclicSucc] using hPhysical.symm
      · simpa [cyclicSucc] using hPhysical
    connector_injective := C.connector_injective
    left_incident := by
      intro i
      fin_cases i
      · exact hShort.2.2
      · simpa using C.left_incident 1
    right_incident := by
      intro i
      fin_cases i
      · simpa [cyclicSucc] using C.right_incident 0
      · simpa only [hPred0] using hShort.2.1
  }
  have hWord : List.ofFn (fun i : Fin 2 => (B.label i, B.connector i)) =
      C.resultWord D pieces := by
    rfl
  exact ⟨1, hk, pieces, hValid, 2, B, hWord⟩

/-- One actual short from the other source occurrence is enough to
construct a global n=2 supreme plan in either cyclic orientation. -/
theorem BigCycle.two_short_at_other_simultaneous
    (C : D.BigCycle 2)
    (k : Fin 2) (hk : D.designated (C.label k))
    (e : E)
    (hShort : C.ShortValid D k (cyclicSucc k) e) :
    C.HasSimultaneousSupreme := by
  fin_cases k
  · exact C.two_short_at_zero_simultaneous D hk e
      (by simpa [cyclicSucc] using hShort)
  · exact C.two_short_at_one_simultaneous D hk e
      (by simpa [cyclicSucc] using hShort)

end OrderOneData
end StructuralRamsey.Girth

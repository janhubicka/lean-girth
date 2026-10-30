import Girth.TrainPositiveCutSequentialAbsorption
import Mathlib.Tactic

/-!
# Length-two physical short replacement retaining a designated occurrence

At two occurrences, predecessor and successor of one occurrence are
the same OTHER index. If that other label is designated, every actual
short physical edge is automatically distinct from the neighboring
labels. Replacing the remaining occurrence by the physical edge is a
literal BigCycle; the untouched designated label discharges A1 at
order one while A2/A3 and twice-order are inherited.

The already checked arbitrary physical short supreme pullback then
transfers any later genuine global supreme plan to the original cycle.
This is precisely the order-one designated-retention interface; the
actual physical witness bridge must still be constructed from the
reduced cut geometry. No appendix.
-/

namespace StructuralRamsey.Girth

/-- At length TWO, the two cyclic neighbours of a specified
occurrence are the other unique occurrence. -/
theorem trainCyclicPred_eq_succ_of_two (k : Fin 2) :
    trainCyclicPred k = cyclicSucc k := by
  fin_cases k <;> decide

namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A physical short replacement of the non-designated occurrence
of a two-occurrence cycle is automatically legal when its other
label is designated and the chosen edge has both physical
incidences. Both neighboring inequalities follow from disjoint
label sorts and are not separate assumptions. -/
theorem BigCycle.replace_physical_two_of_other_designated
    (C : D.BigCycle 2) (hAccept : C.Acceptable)
    (k : Fin 2) (i : I) (e : E)
    (hOther : C.label (cyclicSucc k) = Sum.inl i)
    (hAt : D.Incident (Sum.inr e) (C.connector k))
    (hPred : D.Incident (Sum.inr e)
      (C.connector (trainCyclicPred k))) :
    ∃ H : D.BigCycle 2,
      H.Acceptable ∧ H.twiceOrder = C.twiceOrder ∧
      H.label (cyclicSucc k) = C.label (cyclicSucc k) := by
  have hPredIndex : trainCyclicPred k = cyclicSucc k :=
    trainCyclicPred_eq_succ_of_two k
  have hPrevLabel : C.label (trainCyclicPred k) ≠ Sum.inr e := by
    rw [hPredIndex, hOther]
    intro h
    cases h
  have hNextLabel : (Sum.inr e : I ⊕ E) ≠ C.label (cyclicSucc k) := by
    rw [hOther]
    intro h
    cases h
  have hIndexNe : cyclicSucc k ≠ k := by
    intro h
    exact C.adjacent_ne k (congrArg C.label h.symm)
  let H := C.replaceOne D k (Sum.inr e)
    hPrevLabel hNextLabel hAt hPred
  refine ⟨H, ?_, ?_, ?_⟩
  · exact C.replaceOne_acceptable_of_other_designated
      D k (cyclicSucc k) (Sum.inr e)
      hIndexNe (by rw [hOther]; rfl)
      hPrevLabel hNextLabel hAt hPred hAccept
  · exact C.replaceOne_twiceOrder D k (Sum.inr e)
      hPrevLabel hNextLabel hAt hPred
  · simp [H, BigCycle.replaceOne, BigCycle.relabelSameConnectors,
      BigCycle.replaceLabelAt, hIndexNe]

/-- If a designated label survives an actual physical short
replacement at length two, any global supreme plan on its legal
output pulls back to the original cycle, with exact order retained.
This does not treat local short-piece choices as global plans. -/
theorem BigCycle.supreme_of_physical_two_other_designated
    (C : D.BigCycle 2) (hAccept : C.Acceptable)
    (hLinear : D.LinearPretrain)
    (k : Fin 2) (i : I) (e : E)
    (hOther : C.label (cyclicSucc k) = Sum.inl i)
    (hAt : D.Incident (Sum.inr e) (C.connector k))
    (hPred : D.Incident (Sum.inr e)
      (C.connector (trainCyclicPred k)))
    (hSupreme : ∀ (hPrev : C.label (trainCyclicPred k) ≠ Sum.inr e)
      (hNext : (Sum.inr e : I ⊕ E) ≠ C.label (cyclicSucc k)),
      (C.replaceOne D k (Sum.inr e)
        hPrev hNext hAt hPred).HasSimultaneousSupreme) :
    C.HasSimultaneousSupreme := by
  have hPredIndex := trainCyclicPred_eq_succ_of_two k
  have hPrevLabel : C.label (trainCyclicPred k) ≠ Sum.inr e := by
    rw [hPredIndex, hOther]
    intro h
    cases h
  have hNextLabel : (Sum.inr e : I ⊕ E) ≠ C.label (cyclicSucc k) := by
    rw [hOther]
    intro h
    cases h
  exact C.supreme_pullback_one_physical_short D k e
    hPrevLabel hNextLabel hAt hPred hAccept hLinear
    (hSupreme hPrevLabel hNextLabel)

end OrderOneData
end StructuralRamsey.Girth

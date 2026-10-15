import Girth.TrainSimultaneousSupreme
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Circulation: construct an actual big cycle from a checked finite word

The full PlanProducesBigCycle requirement insists that the flattened
replacement word literally come from a legal BigCycle. Instead of
postulating the cycle or hand-writing a second cyclic indexing system,
check the five defining conditions on the finite word itself:

* length at least two,
* pairwise distinct physical connectors,
* unequal adjacent labels, including the cyclic wrap,
* incidence of each label with its right connector,
* incidence of the next label with that connector.

These conditions are EQUIVALENT to existence of a BigCycle with exactly
that word. The remaining mathematics is proving the conditions from
PlanValid, fresh long wagons and A2--A3.

No appendix hypothesis or new axiom is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Exact conditions for a finite cyclic word of labels and physical
vertex/wagon connectors, indexed by the OUTPUT length. -/
structure CyclicWordChecks
    (word : List ((I ⊕ E) × (V ⊕ P))) : Prop where
  length_ge_two : 2 ≤ word.length
  connector_injective :
    Function.Injective (fun i : Fin word.length => (word.get i).2)
  adjacent_ne : ∀ i : Fin word.length,
    (word.get i).1 ≠ (word.get (cyclicSucc i)).1
  left_incident : ∀ i : Fin word.length,
    D.Incident (word.get i).1 (word.get i).2
  right_incident : ∀ i : Fin word.length,
    D.Incident (word.get (cyclicSucc i)).1 (word.get i).2

/-- Assemble literal word checks into the real BigCycle record. -/
def BigCycle.ofCheckedWord
    (word : List ((I ⊕ E) × (V ⊕ P)))
    (h : D.CyclicWordChecks word) :
    D.BigCycle word.length where
  length_ge_two := h.length_ge_two
  label := fun i => (word.get i).1
  connector := fun i => (word.get i).2
  adjacent_ne := h.adjacent_ne
  connector_injective := h.connector_injective
  left_incident := h.left_incident
  right_incident := h.right_incident

/-- The constructed cycle has literally the original ordered word. -/
theorem BigCycle.ofCheckedWord_word
    (word : List ((I ⊕ E) × (V ⊕ P)))
    (h : D.CyclicWordChecks word) :
    List.ofFn (fun i : Fin word.length =>
      ((D.BigCycle.ofCheckedWord word h).label i,
       (D.BigCycle.ofCheckedWord word h).connector i)) = word := by
  simpa [BigCycle.ofCheckedWord] using (List.ofFn_get word)

/-- Conversely every legal BigCycle satisfies all five checks on its
literal List.ofFn word; this is not a weaker condition. -/
theorem BigCycle.toCyclicWordChecks
    {n : ℕ} (C : D.BigCycle n) :
    D.CyclicWordChecks
      (List.ofFn (fun i : Fin n => (C.label i, C.connector i))) := by
  refine ⟨by simpa using C.length_ge_two, ?_, ?_, ?_, ?_⟩
  · simpa only [List.length_ofFn, List.get_ofFn, Fin.cast_refl]
      using C.connector_injective
  · intro i
    simpa only [List.length_ofFn, List.get_ofFn, Fin.cast_refl]
      using C.adjacent_ne i
  · intro i
    simpa only [List.length_ofFn, List.get_ofFn, Fin.cast_refl]
      using C.left_incident i
  · intro i
    simpa only [List.length_ofFn, List.get_ofFn, Fin.cast_refl]
      using C.right_incident i

/-- A simultaneous plan produces a BigCycle iff its exact flattened
replacement word passes the intrinsic cyclic-word checks. -/
theorem BigCycle.planProducesBigCycle_iff_wordChecks
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) :
    C.PlanProducesBigCycle D pieces ↔
      D.CyclicWordChecks (C.resultWord D pieces) := by
  constructor
  · rintro ⟨m, B, hWord⟩
    rw [← hWord]
    exact B.toCyclicWordChecks D
  · intro h
    exact ⟨(C.resultWord D pieces).length,
      D.BigCycle.ofCheckedWord (C.resultWord D pieces) h,
      D.BigCycle.ofCheckedWord_word (C.resultWord D pieces) h⟩

end StructuralRamsey.Girth.OrderOneData

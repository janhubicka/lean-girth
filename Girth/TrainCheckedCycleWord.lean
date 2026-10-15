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
      ((BigCycle.ofCheckedWord D word h).label i,
       (BigCycle.ofCheckedWord D word h).connector i)) = word := by
  simpa [BigCycle.ofCheckedWord] using (List.ofFn_get word)

/-- Conversely every legal BigCycle satisfies all five checks on its
literal List.ofFn word; this is not a weaker condition. -/
theorem BigCycle.toCyclicWordChecks
    {n : ℕ} (C : D.BigCycle n) :
    D.CyclicWordChecks
      (List.ofFn (fun i : Fin n => (C.label i, C.connector i))) := by
  refine ⟨by simpa using C.length_ge_two, ?_, ?_, ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    have heq : (Fin.cast (by simp) i : Fin n) =
        (Fin.cast (by simp) j : Fin n) :=
      C.connector_injective (by simpa only [List.get_ofFn] using h)
    simpa using congrArg Fin.val heq
  · intro i
    have h := C.adjacent_ne (Fin.cast (by simp) i : Fin n)
    simpa [List.get_ofFn, cyclicSucc, Fin.cast] using h
  · intro i
    have h := C.left_incident (Fin.cast (by simp) i : Fin n)
    simpa [List.get_ofFn, Fin.cast] using h
  · intro i
    have h := C.right_incident (Fin.cast (by simp) i : Fin n)
    simpa [List.get_ofFn, cyclicSucc, Fin.cast] using h

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
      BigCycle.ofCheckedWord D (C.resultWord D pieces) h,
      BigCycle.ofCheckedWord_word D (C.resultWord D pieces) h⟩

end StructuralRamsey.Girth.OrderOneData

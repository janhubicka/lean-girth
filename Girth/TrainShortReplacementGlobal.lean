import Girth.TrainShortReplacementAcceptability

/-!
# Circulation: globally legal short-only relabelling

The circulation cycle-transfer step repeatedly replaces occurrences by genuine
short edges while keeping every connector fixed.  Once the new labels are
known to satisfy the literal BigCycle adjacency and incidence conditions,
there is no further acceptability argument: A2 and A3 depend only on the
connector sequence, the numerical order is unchanged, and at order one A1
reduces exactly to survival of one designated label.

This file packages that reduction.  It deliberately does NOT prove the
segment-specific adjacent-label inequalities; those are the remaining local
legality checks in the circulation proof.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Replace all occurrence labels while keeping the connector sequence
literally unchanged.  The caller supplies only the three genuinely new
BigCycle obligations: adjacent labels differ and both endpoint incidences
remain valid. -/
def BigCycle.relabelSameConnectors
    {n : ℕ} (C : D.BigCycle n)
    (label' : Fin n → I ⊕ E)
    (hAdjacent : ∀ i, label' i ≠ label' (cyclicSucc i))
    (hLeft : ∀ i, D.Incident (label' i) (C.connector i))
    (hRight : ∀ i, D.Incident (label' (cyclicSucc i)) (C.connector i)) :
    D.BigCycle n where
  length_ge_two := C.length_ge_two
  label := label'
  connector := C.connector
  adjacent_ne := hAdjacent
  connector_injective := C.connector_injective
  left_incident := hLeft
  right_incident := hRight

/-- The relabelled cycle has exactly the same numerical order. -/
theorem BigCycle.relabelSameConnectors_twiceOrder
    {n : ℕ} (C : D.BigCycle n)
    (label' : Fin n → I ⊕ E)
    (hAdjacent : ∀ i, label' i ≠ label' (cyclicSucc i))
    (hLeft : ∀ i, D.Incident (label' i) (C.connector i))
    (hRight : ∀ i, D.Incident (label' (cyclicSucc i)) (C.connector i)) :
    (C.relabelSameConnectors D label' hAdjacent hLeft hRight).twiceOrder =
      C.twiceOrder := by
  exact BigCycle.twiceOrder_eq_of_same_connectors D
    (C.relabelSameConnectors D label' hAdjacent hLeft hRight) C (fun _ => rfl)

/-- A globally legal short-only relabelling preserves acceptability.
At order one the only extra obligation is the exact manuscript condition:
some relabelled occurrence is still designated. -/
theorem BigCycle.relabelSameConnectors_acceptable
    {n : ℕ} (C : D.BigCycle n)
    (label' : Fin n → I ⊕ E)
    (hAdjacent : ∀ i, label' i ≠ label' (cyclicSucc i))
    (hLeft : ∀ i, D.Incident (label' i) (C.connector i))
    (hRight : ∀ i, D.Incident (label' (cyclicSucc i)) (C.connector i))
    (hRetain : C.twiceOrder = 2 → ∃ i : Fin n, D.designated (label' i))
    (hAccept : C.Acceptable) :
    (C.relabelSameConnectors D label' hAdjacent hLeft hRight).Acceptable := by
  apply BigCycle.acceptable_of_same_connectors D C
    (C.relabelSameConnectors D label' hAdjacent hLeft hRight)
  · intro i
    rfl
  · intro hOrder
    exact hRetain ((C.relabelSameConnectors_twiceOrder D
      label' hAdjacent hLeft hRight).trans hOrder)
  · exact hAccept

/-- Above order one, A1 is vacuous after any legal same-connector relabelling.
Thus no designation-retention premise is needed. -/
theorem BigCycle.relabelSameConnectors_acceptable_of_order_ne_one
    {n : ℕ} (C : D.BigCycle n)
    (label' : Fin n → I ⊕ E)
    (hAdjacent : ∀ i, label' i ≠ label' (cyclicSucc i))
    (hLeft : ∀ i, D.Incident (label' i) (C.connector i))
    (hRight : ∀ i, D.Incident (label' (cyclicSucc i)) (C.connector i))
    (hOrder : C.twiceOrder ≠ 2)
    (hAccept : C.Acceptable) :
    (C.relabelSameConnectors D label' hAdjacent hLeft hRight).Acceptable := by
  apply C.relabelSameConnectors_acceptable D label'
    hAdjacent hLeft hRight
  · intro h
    exact False.elim (hOrder h)
  · exact hAccept

end StructuralRamsey.Girth.OrderOneData

import Girth.TrainShortReplacementNeighbour

/-!
# Circulation: simultaneous short-only replacement is automatically legal

For a cycle of length at least three, choose at each occurrence either no
replacement or one actual edge incident with the two old boundary connectors.
Nothing else is required for global legality.  The connector sequence is
unchanged.  The A2--A3 theorem that one actual edge cannot meet three distinct
connector positions rules out every possible adjacent-label collision,
including collisions between two newly chosen edges.

Thus a short-only simultaneous replacement produces an acceptable cycle of
the same order.  This is the exact global legality statement used in the
multi-segment part of the circulated cycle-transfer proof.  The exceptional
two-occurrence/order-one case remains handled by its dedicated bridge theorem.
-/

namespace StructuralRamsey.Girth
namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Final occurrence labels for a family of optional short replacements. -/
def BigCycle.shortRelabel
    {n : ℕ} (C : D.BigCycle n) (replace : Fin n → Option E) :
    Fin n → I ⊕ E :=
  fun i => match replace i with
    | none => C.label i
    | some e => .inr e

/-- The only local data required of every chosen short edge: incidence with
the predecessor and current boundary connectors. -/
def BigCycle.ShortRelabelValid
    {n : ℕ} (C : D.BigCycle n) (replace : Fin n → Option E) : Prop :=
  ∀ (i : Fin n) (e : E), replace i = some e →
    D.Incident (.inr e) (C.connector (trainCyclicPred i)) ∧
    D.Incident (.inr e) (C.connector i)

/-- At length at least three, all final neighbouring labels are automatically
different.  No pairwise distinctness assumption on the chosen edges is needed. -/
theorem BigCycle.shortRelabel_adjacent
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (replace : Fin n → Option E)
    (hValid : C.ShortRelabelValid D replace) :
    ∀ i : Fin n,
      C.shortRelabel D replace i ≠
        C.shortRelabel D replace (cyclicSucc i) := by
  intro i
  cases hi : replace i with
  | none =>
      cases hs : replace (cyclicSucc i) with
      | none =>
          simpa [BigCycle.shortRelabel, hi, hs] using C.adjacent_ne i
      | some f =>
          have hf := hValid (cyclicSucc i) f hs
          have hne := C.shortEdge_ne_neighbors D hAccept hn
            (cyclicSucc i) f hf.1 hf.2
          have hpred :
              trainCyclicPred (cyclicSucc i) = i :=
            trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i
          have h : C.label i ≠ (.inr f : I ⊕ E) := by
            simpa [hpred] using hne.1
          simpa [BigCycle.shortRelabel, hi, hs] using h
  | some e =>
      have he := hValid i e hi
      cases hs : replace (cyclicSucc i) with
      | none =>
          have hne := C.shortEdge_ne_neighbors D hAccept hn i e he.1 he.2
          simpa [BigCycle.shortRelabel, hi, hs] using hne.2
      | some f =>
          intro hef
          have hef' : e = f := Sum.inr.inj (by
            simpa [BigCycle.shortRelabel, hi, hs] using hef)
          subst f
          have hf := hValid (cyclicSucc i) e hs
          have hSuccSelf : i ≠ cyclicSucc i := by
            intro h
            exact C.adjacent_ne i (congrArg C.label h)
          have hPredSelf : trainCyclicPred i ≠ i := by
            intro h
            have hsi := cyclicSucc_trainCyclicPred_of_two_le
              C.length_ge_two i
            rw [h] at hsi
            exact hSuccSelf hsi.symm
          have hPredSucc :
              trainCyclicPred i ≠ cyclicSucc i :=
            trainCyclicPred_ne_cyclicSucc_of_three_le hn i
          exact C.not_edge_incident_three_distinct D hAccept e
            (trainCyclicPred i) i (cyclicSucc i)
            hPredSelf hPredSucc hSuccSelf he.1 he.2 hf.2

/-- The final relabelled word is a genuine BigCycle with exactly the old
connector sequence. -/
def BigCycle.shortRelabelCycle
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (replace : Fin n → Option E)
    (hValid : C.ShortRelabelValid D replace) :
    D.BigCycle n :=
  C.relabelSameConnectors D (C.shortRelabel D replace)
    (C.shortRelabel_adjacent D hAccept hn replace hValid)
    (by
      intro i
      cases hi : replace i with
      | none =>
          simpa [BigCycle.shortRelabel, hi] using C.left_incident i
      | some e =>
          have he := hValid i e hi
          simpa [BigCycle.shortRelabel, hi] using he.2)
    (by
      intro i
      cases hs : replace (cyclicSucc i) with
      | none =>
          simpa [BigCycle.shortRelabel, hs] using C.right_incident i
      | some e =>
          have he := hValid (cyclicSucc i) e hs
          have hpred :
              trainCyclicPred (cyclicSucc i) = i :=
            trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i
          simpa [BigCycle.shortRelabel, hs, hpred] using he.1)

/-- Simultaneous short-only replacement preserves the numerical order. -/
theorem BigCycle.shortRelabelCycle_twiceOrder
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (replace : Fin n → Option E)
    (hValid : C.ShortRelabelValid D replace) :
    (C.shortRelabelCycle D hAccept hn replace hValid).twiceOrder =
      C.twiceOrder := by
  exact C.relabelSameConnectors_twiceOrder D
    (C.shortRelabel D replace)
    (C.shortRelabelCycle D hAccept hn replace hValid).adjacent_ne
    (C.shortRelabelCycle D hAccept hn replace hValid).left_incident
    (C.shortRelabelCycle D hAccept hn replace hValid).right_incident

/-- Simultaneous short-only replacement of a cycle of length at least three
preserves full acceptability.  A1 needs no separate treatment because such a
cycle is not order one. -/
theorem BigCycle.shortRelabelCycle_acceptable
    {n : ℕ} (C : D.BigCycle n) (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (replace : Fin n → Option E)
    (hValid : C.ShortRelabelValid D replace) :
    (C.shortRelabelCycle D hAccept hn replace hValid).Acceptable := by
  exact C.relabelSameConnectors_acceptable_of_order_ne_one D
    (C.shortRelabel D replace)
    (C.shortRelabelCycle D hAccept hn replace hValid).adjacent_ne
    (C.shortRelabelCycle D hAccept hn replace hValid).left_incident
    (C.shortRelabelCycle D hAccept hn replace hValid).right_incident
    (C.twiceOrder_ne_two_of_three_le_length D hn)
    hAccept

end OrderOneData
end StructuralRamsey.Girth

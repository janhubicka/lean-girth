import Girth.TrainSystemCutGirthTwo
import Girth.TrainCheckedCycleWord
import Mathlib.Tactic

/-!
# A chordless labelled wagon cycle as a temporary designated-copy cycle

A shortest labelled cut cycle is first treated as a big cycle in an
auxiliary pretrain: each real wagon is designated as its own complete
edge family. An existing arbitrary-replacement theorem can then be
used for the physical short/long edge expansion at source length >=3.

This file constructs the EXACT acceptable auxiliary source cycle and
its order. No fake physical edges are inserted. The chordless-window
premise and the later edge-only retyping and expansion are explicit
separate obligations. No appendix is involved.
-/

namespace StructuralRamsey.Girth

universe v

/-- Name each actual wagon as a temporary designated copy. -/
def OrderOneData.wagonSeed
    {V E I P : Type v} (D : OrderOneData V E I P) :
    OrderOneData V E P P where
  edgeCarrier := D.edgeCarrier
  copyCarrier := fun p => {x | D.WagonVertex p x}
  copyEdges := fun p => {e | D.parent e = p}
  parent := D.parent

/-- Physical and wagon linearity are unchanged by temporary naming. -/
theorem OrderOneData.wagonSeed_linear_iff
    {V E I P : Type v} (D : OrderOneData V E I P) :
    (D.wagonSeed).LinearPretrain ↔ D.LinearPretrain := Iff.rfl

namespace OrderOneData

variable {V E I P : Type v} (D : OrderOneData V E I P)

private theorem fin_ne_cyclicSucc
    {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : i ≠ cyclicSucc i := by
  intro he
  have hv := congrArg Fin.val he
  change i.val = (i.val + 1) % n at hv
  have hle : i.val + 1 ≤ n := by have := i.isLt; omega
  rcases lt_or_eq_of_le hle with hl | heq
  · rw [Nat.mod_eq_of_lt hl] at hv
    omega
  · rw [heq, Nat.mod_self] at hv
    omega

/-- A labelled cut cycle is a legal big cycle in the AUXILIARY
wagon-as-designated-copy pretrain. -/
def labelledWagonCycle.toWagonSeedBigCycle
    (C : LabelledBergeCycle (fun p : P => {x : V | D.WagonVertex p x})) :
    (D.wagonSeed).BigCycle C.length where
  length_ge_two := C.hlength
  label := fun i => Sum.inl (C.label i)
  connector := fun i => Sum.inl (C.vertex i)
  adjacent_ne := by
    intro i he
    have hh : C.label i = C.label (cyclicSucc i) := Sum.inl.inj he
    exact (D.fin_ne_cyclicSucc C.hlength i) (C.label_injective hh)
  connector_injective := by
    intro i j h
    exact C.vertex_injective (Sum.inl.inj h)
  left_incident := by
    intro i
    change D.WagonVertex (C.label i) (C.vertex i)
    exact C.left_mem i
  right_incident := by
    intro i
    change D.WagonVertex (C.label (cyclicSucc i)) (C.vertex i)
    exact C.right_mem i

/-- With only vertex connectors and length at least three, A1 and A2
are automatic; A3 is precisely the no-chord vertex-contact window. -/
theorem BigCycle.acceptable_of_vertex_only_chordless
    {J : Type v} (T : OrderOneData V E J P)
    {n : ℕ} (C : T.BigCycle n) (hn : 3 ≤ n)
    (hVertex : ∀ j : Fin n, ∃ x : V, C.connector j = Sum.inl x)
    (hChordless : ∀ p : P, ∃ i : Fin n,
      ∀ j : Fin n, C.InWagonAt p j →
        j = i ∨ j = cyclicSucc i) :
    C.Acceptable := by
  have hA1 : C.A1 := by
    intro hOrder
    have hLen := C.length_eq_two_of_order_one T hOrder
    omega
  have hA2 : C.A2 := by
    constructor
    · intro i p hi j hj
      obtain ⟨x, hx⟩ := hVertex i
      rw [hx] at hi
      cases hi
    · intro i p x y hi hPrev hNext hDiff hx hy
      obtain ⟨z, hz⟩ := hVertex i
      rw [hz] at hi
      cases hi
  exact ⟨hA1, hA2, by
    intro p _
    exact hChordless p⟩

/-- The temporary designated-wagon source is acceptable when the
shortest-cut incidence data have the literal no-chord window. -/
theorem labelledWagonCycle.wagonSeed_acceptable_of_chordless
    (C : LabelledBergeCycle (fun p : P => {x : V | D.WagonVertex p x}))
    (hn : 3 ≤ C.length)
    (hChordless : ∀ p : P, ∃ i : Fin C.length,
      ∀ j : Fin C.length,
        D.WagonVertex p (C.vertex j) →
        j = i ∨ j = cyclicSucc i) :
    (C.toWagonSeedBigCycle D).Acceptable := by
  have hVertex : ∀ j : Fin C.length,
      ∃ x : V, (C.toWagonSeedBigCycle D).connector j = Sum.inl x := by
    intro j
    exact ⟨C.vertex j, rfl⟩
  have hA3 : ∀ p : P, ∃ i : Fin C.length,
    ∀ j : Fin C.length, (C.toWagonSeedBigCycle D).InWagonAt p j →
      j = i ∨ j = cyclicSucc i := by
    intro p
    obtain ⟨i, hi⟩ := hChordless p
    refine ⟨i, ?_⟩
    intro j hj
    obtain ⟨x, hx, hw⟩ := hj
    change (Sum.inl (C.vertex j) : V ⊕ P) = Sum.inl x at hx
    have he : x = C.vertex j := (Sum.inl.inj hx).symm
    exact hi j (by simpa [he] using hw)
  exact (C.toWagonSeedBigCycle D).acceptable_of_vertex_only_chordless
    (D.wagonSeed) hn hVertex hA3

/-- A source with only vertex connectors has twice-order exactly twice
its number of occurrences. -/
theorem BigCycle.twiceOrder_of_vertex_only
    {J : Type v} (T : OrderOneData V E J P)
    {n : ℕ} (C : T.BigCycle n)
    (hVertex : ∀ j : Fin n, ∃ x : V, C.connector j = Sum.inl x) :
    C.twiceOrder = 2 * n := by
  have hw : ∀ j : Fin n,
      twiceOccurrenceWeight (connectorKind (C.connector j))
        (connectorKind (C.connector (cyclicSucc j))) = 2 := by
    intro j
    obtain ⟨x, hx⟩ := hVertex j
    obtain ⟨y, hy⟩ := hVertex (cyclicSucc j)
    simp [hx, hy, connectorKind, twiceOccurrenceWeight]
  simp only [BigCycle.twiceOrder]
  simp_rw [hw]
  simp [mul_comm]

/-- The artificial wagon-cycle seed has order equal to the length of
the original labelled cut cycle, before any physical expansion. -/
theorem labelledWagonCycle.wagonSeed_twiceOrder
    (C : LabelledBergeCycle (fun p : P => {x : V | D.WagonVertex p x})) :
    (C.toWagonSeedBigCycle D).twiceOrder = 2 * C.length := by
  apply (C.toWagonSeedBigCycle D).twiceOrder_of_vertex_only (D.wagonSeed)
  intro j
  exact ⟨C.vertex j, rfl⟩

end OrderOneData
end StructuralRamsey.Girth

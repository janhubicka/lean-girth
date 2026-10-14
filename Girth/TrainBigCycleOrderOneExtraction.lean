import Girth.TrainOrderOneBridge
import Girth.TrainCycleWeights
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Circulation: the manuscript's big-cycle syntax and the order-one reduction

This is the *circulation* acceptable-cycle language (A1)--(A3), not an
appendix theorem. Labels retain the disjoint union of designated copies
and actual edge labels, even when both denote one physical edge.

At order one the cycle has two occurrences with opposite connector kinds.
The two special A2 side positions coincide, so its extra no-ambient-edge
clause is vacuous; A3 is automatic because there are only two positions.

We encode every cyclic occurrence and its two connector incidences.
For supreme copies we first record the necessary short/long replacement
piece for each differently labelled occurrence. The additional global
simultaneous-replacement condition of the manuscript is NOT yet encoded;
a truly supreme copy necessarily has these local pieces. Thus
LocalPieceSystemBound is explicitly a WEAKER, necessary consequence of
full system girth, not a replacement definition of full system girth.
-/

namespace StructuralRamsey.Girth

/-- Cyclic predecessor at a nonempty finite index type. -/
def trainCyclicPred {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A connector is a real vertex or a wagon, as in the manuscript. -/
def Incident (a : I ⊕ E) : V ⊕ P → Prop
  | .inl x => x ∈ D.carrier a
  | .inr p => D.Meets a p

/-- The vertex belongs to the full carrier of a wagon. -/
def WagonVertex (p : P) (x : V) : Prop :=
  ∃ e : E, D.parent e = p ∧ x ∈ D.edgeCarrier e

/-- The ambient edge relation joins a specified pair of vertices. -/
def PairEdge (x y : V) : Prop :=
  ∃ e : E, x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier e

/-- The two kinds of connectors used by the twice-order weight. -/
def connectorKind : V ⊕ P → CycleConnectorKind
  | .inl _ => .vertex
  | .inr _ => .wagon

/-- A cyclic alternating sequence of labels and connectors. Adjacent
labels, but not all labels, must be distinct. -/
structure BigCycle (n : ℕ) where
  length_ge_two : 2 ≤ n
  label : Fin n → I ⊕ E
  connector : Fin n → V ⊕ P
  adjacent_ne : ∀ i, label i ≠ label (cyclicSucc i)
  connector_injective : Function.Injective connector
  left_incident : ∀ i, D.Incident (label i) (connector i)
  right_incident : ∀ i, D.Incident (label (cyclicSucc i)) (connector i)

namespace BigCycle

variable {D} {n : ℕ} (C : D.BigCycle n)

/-- Twice the manuscript order, avoiding division by two. -/
def twiceOrder : ℕ :=
  ∑ i : Fin n, twiceOccurrenceWeight
    (connectorKind (C.connector i))
    (connectorKind (C.connector (cyclicSucc i)))

/-- Locations M_C(W) of vertex connectors in the carrier of W. -/
def InWagonAt (p : P) (j : Fin n) : Prop :=
  ∃ x : V, C.connector j = Sum.inl x ∧ D.WagonVertex p x

/-- (A1): every order-one acceptable cycle has a designated label. -/
def A1 : Prop :=
  C.twiceOrder = 2 → ∃ i : Fin n, D.designated (C.label i)

/-- (A2): wagon connectors control vertex positions, including the
ambient-edge prohibition when both neighbouring positions are distinct. -/
def A2 : Prop :=
  (∀ (i : Fin n) (p : P), C.connector i = Sum.inr p →
    ∀ j : Fin n, C.InWagonAt p j →
      j = trainCyclicPred i ∨ j = cyclicSucc i) ∧
  (∀ (i : Fin n) (p : P) (x y : V),
    C.connector i = Sum.inr p →
    C.connector (trainCyclicPred i) = Sum.inl x →
    C.connector (cyclicSucc i) = Sum.inl y →
    trainCyclicPred i ≠ cyclicSucc i →
    D.WagonVertex p x → D.WagonVertex p y →
    ¬ D.PairEdge x y)

/-- (A3): nonconnector wagons have all their vertex positions inside
some two consecutive cyclic positions. -/
def A3 : Prop :=
  ∀ p : P, (∀ i : Fin n, C.connector i ≠ Sum.inr p) →
    ∃ i : Fin n, ∀ j : Fin n, C.InWagonAt p j →
      j = i ∨ j = cyclicSucc i

def Acceptable : Prop := C.A1 ∧ C.A2 ∧ C.A3

end BigCycle

/-- A short piece is one actual edge of the supreme label with exactly
the prescribed two boundary connectors. -/
def ShortPiece (a : I ⊕ E) (q r : V ⊕ P) : Prop :=
  ∃ e : E, e ∈ D.edges a ∧
    D.Incident (.inr e) q ∧ D.Incident (.inr e) r

/-- A legal long piece has two vertex boundaries, distinct edges of
one wagon, and no ambient edge through both boundary vertices. -/
def LongPiece (a : I ⊕ E) (q r : V ⊕ P) : Prop :=
  ∃ (x y : V) (w : P) (e f : E),
    q = Sum.inl x ∧ r = Sum.inl y ∧
    e ∈ D.edges a ∧ f ∈ D.edges a ∧ e ≠ f ∧
    D.parent e = w ∧ D.parent f = w ∧
    x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier f ∧
    ¬ D.PairEdge x y

/-- Every truly supreme copy must supply such a piece for every
differently labelled occurrence. This local condition does not yet
encode the simultaneous validity of all replacements. -/
def BigCycle.HasLocalSupreme {n : ℕ} (C : D.BigCycle n) : Prop :=
  ∃ k : Fin n, D.designated (C.label k) ∧
    ∀ j : Fin n, C.label j ≠ C.label k →
      D.ShortPiece (C.label k)
          (C.connector (trainCyclicPred j)) (C.connector j) ∨
      D.LongPiece (C.label k)
          (C.connector (trainCyclicPred j)) (C.connector j)

/-- The weak local-piece consequence that any full system-girth
bound would supply. We deliberately do not call this full Girth. -/
def LocalPieceSystemBound (q : ℕ) : Prop :=
  ∀ (n : ℕ) (C : D.BigCycle n), C.Acceptable →
    C.twiceOrder ≤ 2 * q → C.HasLocalSupreme

/-- At length two the predecessor and successor coincide. -/
theorem finTwo_pred_eq_succ (i : Fin 2) :
    trainCyclicPred i = cyclicSucc i := by
  fin_cases i <;> decide

/-- (A2) is automatic at length two, including its no-edge clause. -/
theorem twoCycle_A2 (C : D.BigCycle 2) : C.A2 := by
  constructor
  · intro i p hi j hj
    rcases hj with ⟨x, hx, _⟩
    fin_cases i <;> fin_cases j <;>
      simp_all [cyclicSucc, trainCyclicPred]
  · intro i p x y _ _ _ hne _ _
    exact False.elim (hne (finTwo_pred_eq_succ i))

/-- (A3) is automatic at length two: the positions are consecutive. -/
theorem twoCycle_A3 (C : D.BigCycle 2) : C.A3 := by
  intro p _
  refine ⟨0, ?_⟩
  intro j _
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (by decide)

/-- The two-occurrence mixed-boundary cycle A x B W is a genuine
instance of the general labelled big-cycle syntax. -/
def Cycle.toBigCycle (C : D.Cycle) : D.BigCycle 2 where
  length_ge_two := by omega
  label := ![C.left, C.right]
  connector := ![Sum.inl C.vertex, Sum.inr C.wagon]
  adjacent_ne := by
    intro i
    fin_cases i
    · simpa [cyclicSucc] using C.different
    · simpa [cyclicSucc] using C.different.symm
  connector_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all
  left_incident := by
    intro i
    fin_cases i
    · exact C.left_vertex
    · exact C.right_meets
  right_incident := by
    intro i
    fin_cases i
    · simpa [cyclicSucc, Incident] using C.right_vertex
    · simpa [cyclicSucc, Incident] using C.left_meets

/-- Both occurrences are mixed; the manuscript order is exactly one. -/
theorem Cycle.toBigCycle_twiceOrder (C : D.Cycle) :
    C.toBigCycle.twiceOrder = 2 := by
  simp [BigCycle.twiceOrder, connectorKind, Cycle.toBigCycle,
    Fin.sum_univ_two, cyclicSucc, twiceOccurrenceWeight]

/-- The canonical order-one cycle satisfies all of (A1)--(A3).
No ambient non-edge assumption is hidden in the length-two case. -/
theorem Cycle.toBigCycle_acceptable (C : D.Cycle) :
    C.toBigCycle.Acceptable := by
  refine ⟨?_, D.twoCycle_A2 C.toBigCycle, D.twoCycle_A3 C.toBigCycle⟩
  intro _
  rcases C.has_designated with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

/-- Any legal piece with a vertex and a wagon boundary is short,
and therefore supplies exactly the desired common edge. -/
theorem piece_mixed_bridge (a : I ⊕ E) (x : V) (p : P)
    (h : D.ShortPiece a (Sum.inl x) (Sum.inr p) ∨
      D.LongPiece a (Sum.inl x) (Sum.inr p)) :
    D.Bridge a x p := by
  rcases h with ⟨e, he, hxe, hp⟩ | h
  · rcases hp with ⟨f, hf, hfp⟩
    have hfe : f = e := hf
    subst f
    exact ⟨e, he, hfp, hxe⟩
  · rcases h with ⟨x', y', w, e, f, _, hr, _⟩
    cases hr

theorem piece_mixed_bridge_reverse (a : I ⊕ E) (x : V) (p : P)
    (h : D.ShortPiece a (Sum.inr p) (Sum.inl x) ∨
      D.LongPiece a (Sum.inr p) (Sum.inl x)) :
    D.Bridge a x p := by
  rcases h with ⟨e, he, hp, hxe⟩ | h
  · rcases hp with ⟨f, hf, hfp⟩
    have hfe : f = e := hf
    subst f
    exact ⟨e, he, hfp, hxe⟩
  · rcases h with ⟨x', y', w, e, f, hq, _⟩
    cases hq

/-- A locally supreme copy of the canonical length-two big cycle
supplies the exact bridge in the existing OrderOneData.Bound. -/
theorem Cycle.hasSupreme_of_bigCycle_localSupreme
    (C : D.Cycle) (h : C.toBigCycle.HasLocalSupreme) :
    C.HasSupreme := by
  rcases h with ⟨i, hi, hpieces⟩
  fin_cases i
  · have h : C.toBigCycle.label 1 ≠ C.toBigCycle.label 0 := by
      exact C.different.symm
    have hp := hpieces 1 h
    have hb : D.Bridge C.left C.vertex C.wagon := by
      exact D.piece_mixed_bridge
        C.left C.vertex C.wagon (by simpa [Cycle.toBigCycle,
          trainCyclicPred] using hp)
    exact Or.inl ⟨hi, hb⟩
  · have h : C.toBigCycle.label 0 ≠ C.toBigCycle.label 1 :=
      C.different
    have hp := hpieces 0 h
    have hb : D.Bridge C.right C.vertex C.wagon := by
      exact D.piece_mixed_bridge_reverse
        C.right C.vertex C.wagon (by simpa [Cycle.toBigCycle,
          trainCyclicPred] using hp)
    exact Or.inr ⟨hi, hb⟩

/-- The explicitly encoded (A1)--(A3) cycle bound, together with
the necessary local-piece consequence of supremeness, yields the
order-one bridge. No axiom about bridges is inserted. -/
theorem bound_of_localPieceSystemBound
    (h : D.LocalPieceSystemBound 1) : D.Bound := by
  intro C
  exact Cycle.hasSupreme_of_bigCycle_localSupreme D C
    (h 2 C.toBigCycle (C.toBigCycle_acceptable)
      (by rw [C.toBigCycle_twiceOrder]))

end OrderOneData
end StructuralRamsey.Girth

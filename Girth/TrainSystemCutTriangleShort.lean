import Girth.TrainSystemCutGirthTwo
import Girth.TrainBigCycleOrderBudget
import Mathlib.Tactic

/-!
# From a physical three-wagon triangle with short blocks to a big cycle

This handles the *all-short* case of the shortest-labelled-cut expansion:
each wagon contains one actual physical edge joining its two boundary
vertices. The parent labels and three distinct vertices are retained.
The constructed big cycle is literal, acceptable, and consists solely
of one-edge labels; its twice-order is six.

The general expansion also needs to handle wagons whose two boundary
vertices cannot be joined by a single edge. Those require legal long
pieces and a variable-length cyclic word; this module does not assume
or provide that more difficult construction.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Three distinct connector vertices cannot all belong to an ambient
wagon when two different cycle wagons contain x,z and x,y respectively.
This uses FULL wagon-carrier linearity rather than edge linearity alone. -/
theorem no_three_vertex_wagon_of_two_pairs
    (hLinear : D.LinearPretrain)
    (a b : P) (hab : a ≠ b)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z)
    (hax : D.WagonVertex a x) (haz : D.WagonVertex a z)
    (hbx : D.WagonVertex b x) (hby : D.WagonVertex b y) :
    ∀ p : P, ¬ (D.WagonVertex p x ∧
      D.WagonVertex p y ∧ D.WagonVertex p z) := by
  intro p hp
  rcases hp with ⟨hpx, hpy, hpz⟩
  by_cases heq : p = a
  · subst p
    have he : x = y :=
      (hLinear.2 a b hab) ⟨hpx, hbx⟩ ⟨hpy, hby⟩
    exact hxy he
  · have he : x = z :=
      (hLinear.2 p a heq) ⟨hpx, hax⟩ ⟨hpz, haz⟩
    exact hxz he

/-- A literal three-occurrence cycle with three vertex connectors is
acceptable if no ambient wagon contains all three vertices.  A2 is
vacuous and A3 is the missing-one-of-three condition. -/
theorem BigCycle.three_vertices_acceptable_of_no_triple
    (B : D.BigCycle 3) (x y z : V)
    (h0 : B.connector 0 = Sum.inl x)
    (h1 : B.connector 1 = Sum.inl y)
    (h2 : B.connector 2 = Sum.inl z)
    (hNo : ∀ p : P, ¬ (D.WagonVertex p x ∧
      D.WagonVertex p y ∧ D.WagonVertex p z)) :
    B.Acceptable := by
  have hA1 : B.A1 := by
    intro h
    have hLen := B.length_eq_two_of_order_one D h
    omega
  have hA2 : B.A2 := by
    constructor
    · intro i p hi j hj
      fin_cases i
      · change B.connector (0 : Fin 3) = Sum.inr p at hi
        rw [h0] at hi
        cases hi
      · change B.connector (1 : Fin 3) = Sum.inr p at hi
        rw [h1] at hi
        cases hi
      · change B.connector (2 : Fin 3) = Sum.inr p at hi
        rw [h2] at hi
        cases hi
    · intro i p u v hi hPrev hNext hDiff hp hv
      fin_cases i
      · change B.connector (0 : Fin 3) = Sum.inr p at hi
        rw [h0] at hi
        cases hi
      · change B.connector (1 : Fin 3) = Sum.inr p at hi
        rw [h1] at hi
        cases hi
      · change B.connector (2 : Fin 3) = Sum.inr p at hi
        rw [h2] at hi
        cases hi
  have hxContact : ∀ p : P, B.InWagonAt p (0 : Fin 3) →
      D.WagonVertex p x := by
    intro p h
    obtain ⟨u, hu, hw⟩ := h
    rw [h0] at hu
    have he : u = x := Sum.inl.inj hu.symm
    simpa [he] using hw
  have hyContact : ∀ p : P, B.InWagonAt p (1 : Fin 3) →
      D.WagonVertex p y := by
    intro p h
    obtain ⟨u, hu, hw⟩ := h
    rw [h1] at hu
    have he : u = y := Sum.inl.inj hu.symm
    simpa [he] using hw
  have hzContact : ∀ p : P, B.InWagonAt p (2 : Fin 3) →
      D.WagonVertex p z := by
    intro p h
    obtain ⟨u, hu, hw⟩ := h
    rw [h2] at hu
    have he : u = z := Sum.inl.inj hu.symm
    simpa [he] using hw
  have hA3 : B.A3 := by
    intro p _
    by_cases hx : D.WagonVertex p x
    · by_cases hy : D.WagonVertex p y
      · have hz : ¬ D.WagonVertex p z :=
          fun hz => hNo p ⟨hx, hy, hz⟩
        refine ⟨(0 : Fin 3), ?_⟩
        intro j hj
        fin_cases j
        · exact Or.inl rfl
        · exact Or.inr (by decide)
        · exact (hz (hzContact p hj)).elim
      · refine ⟨(2 : Fin 3), ?_⟩
        intro j hj
        fin_cases j
        · exact Or.inr (by decide)
        · exact (hy (hyContact p hj)).elim
        · exact Or.inl rfl
    · refine ⟨(1 : Fin 3), ?_⟩
      intro j hj
      fin_cases j
      · exact (hx (hxContact p hj)).elim
      · exact Or.inl rfl
      · exact Or.inr (by decide)
  exact ⟨hA1, hA2, hA3⟩

/-- An all-short triangle of three different physical wagon labels
becomes a REAL acceptable edge-only BigCycle of order three. -/
theorem three_short_wagons_bigCycle
    (hLinear : D.LinearPretrain)
    (a b c : P) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (x y z : V) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (e0 e1 e2 : E)
    (hp0 : D.parent e0 = a) (hp1 : D.parent e1 = b)
    (hp2 : D.parent e2 = c)
    (hx0 : x ∈ D.edgeCarrier e0) (hz0 : z ∈ D.edgeCarrier e0)
    (hx1 : x ∈ D.edgeCarrier e1) (hy1 : y ∈ D.edgeCarrier e1)
    (hy2 : y ∈ D.edgeCarrier e2) (hz2 : z ∈ D.edgeCarrier e2) :
    ∃ B : D.BigCycle 3, B.Acceptable ∧ B.twiceOrder = 6 ∧
      (∀ i : Fin 3, ∃ e : E, B.label i = Sum.inr e) := by
  have he01 : e0 ≠ e1 := by
    intro he
    apply hab
    calc a = D.parent e0 := hp0.symm
         _ = D.parent e1 := congrArg D.parent he
         _ = b := hp1
  have he12 : e1 ≠ e2 := by
    intro he
    apply hbc
    calc b = D.parent e1 := hp1.symm
         _ = D.parent e2 := congrArg D.parent he
         _ = c := hp2
  have he20 : e2 ≠ e0 := by
    intro he
    apply hca
    calc c = D.parent e2 := hp2.symm
         _ = D.parent e0 := congrArg D.parent he
         _ = a := hp0
  let B : D.BigCycle 3 := {
    length_ge_two := by omega
    label := ![Sum.inr e0, Sum.inr e1, Sum.inr e2]
    connector := ![Sum.inl x, Sum.inl y, Sum.inl z]
    adjacent_ne := by
      intro i
      fin_cases i
      · change (Sum.inr e0 : I ⊕ E) ≠ Sum.inr e1
        exact fun h => he01 (Sum.inr.inj h)
      · change (Sum.inr e1 : I ⊕ E) ≠ Sum.inr e2
        exact fun h => he12 (Sum.inr.inj h)
      · change (Sum.inr e2 : I ⊕ E) ≠ Sum.inr e0
        exact fun h => he20 (Sum.inr.inj h)
    connector_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [hxy, hyz, hzx]
    left_incident := by
      intro i
      fin_cases i
      · change x ∈ D.edgeCarrier e0
        exact hx0
      · change y ∈ D.edgeCarrier e1
        exact hy1
      · change z ∈ D.edgeCarrier e2
        exact hz2
    right_incident := by
      intro i
      fin_cases i
      · change x ∈ D.edgeCarrier e1
        exact hx1
      · change y ∈ D.edgeCarrier e2
        exact hy2
      · change z ∈ D.edgeCarrier e0
        exact hz0 }
  have hNo : ∀ p : P, ¬ (D.WagonVertex p x ∧
      D.WagonVertex p y ∧ D.WagonVertex p z) :=
    D.no_three_vertex_wagon_of_two_pairs hLinear a b hab x y z hxy
      (Ne.symm hzx) ⟨e0, hp0, hx0⟩ ⟨e0, hp0, hz0⟩
      ⟨e1, hp1, hx1⟩ ⟨e1, hp1, hy1⟩
  have h0 : B.connector 0 = Sum.inl x := rfl
  have h1 : B.connector 1 = Sum.inl y := rfl
  have h2 : B.connector 2 = Sum.inl z := rfl
  have hAccept : B.Acceptable :=
    B.three_vertices_acceptable_of_no_triple D x y z h0 h1 h2 hNo
  have hOrder : B.twiceOrder = 6 := by
    simp [B, BigCycle.twiceOrder, Fin.sum_univ_three,
      cyclicSucc, connectorKind, twiceOccurrenceWeight]
  have hOnly : ∀ i : Fin 3, ∃ e : E, B.label i = Sum.inr e := by
    intro i
    fin_cases i
    · exact ⟨e0, rfl⟩
    · exact ⟨e1, rfl⟩
    · exact ⟨e2, rfl⟩
  exact ⟨B, hAccept, hOrder, hOnly⟩

/-- A full system-girth bound at cutoff at least three excludes a
three-wagon labelled cut triangle whose boundary pairs are all actual
edges. The remaining long-block cases are not asserted. -/
theorem no_three_short_wagons_of_fullSystemGirth
    (hLinear : D.LinearPretrain)
    (q : ℕ) (hq : 3 ≤ q) (hFull : D.FullSystemGirthGT q)
    (a b c : P) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (x y z : V) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (e0 e1 e2 : E)
    (hp0 : D.parent e0 = a) (hp1 : D.parent e1 = b)
    (hp2 : D.parent e2 = c)
    (hx0 : x ∈ D.edgeCarrier e0) (hz0 : z ∈ D.edgeCarrier e0)
    (hx1 : x ∈ D.edgeCarrier e1) (hy1 : y ∈ D.edgeCarrier e1)
    (hy2 : y ∈ D.edgeCarrier e2) (hz2 : z ∈ D.edgeCarrier e2) : False := by
  obtain ⟨B, hAccept, hOrder, hOnly⟩ :=
    D.three_short_wagons_bigCycle hLinear
      a b c hab hbc hca x y z hxy hyz hzx
      e0 e1 e2 hp0 hp1 hp2 hx0 hz0 hx1 hy1 hy2 hz2
  exact B.false_of_acceptable_edgeOnly_fullSystemGirth D q hFull
    hAccept (by omega) hOnly

end StructuralRamsey.Girth.OrderOneData

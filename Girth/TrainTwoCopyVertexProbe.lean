import Girth.TrainBigCycleOrderBudget
import Girth.TrainBigCycleTwoWagonObstruction
import Mathlib.Tactic

/-!
# Circulation: the two-vertex edge probe for two-copy symmetry

If a designated copy contains two distinct vertices x,y and there is
an actual ambient edge e through the pair, the cycle A x e⁺ y is an
acceptable order-two cycle with A the ONLY designated occurrence.

Hence the order-two system bound forces A to possess a short or long
piece with those vertex boundaries. If another designated copy B has
a SHORT piece through x,y, we may use its physical edge for this probe,
establishing the short-witness case of two-copy symmetry.

The long-witness case needs the distinct order-two cycle
A x e₁⁺ W e₂⁺ y and is a separate circulation obligation.
No appendix or new global Ramsey assertion is involved.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The canonical two-vertex probe with one designated label and one
actual physical edge label; their labels remain different even when
their physical vertex carriers coincide. -/
def twoVertexEdgeProbe
    (i : I) (e : E) (x y : V)
    (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hex : x ∈ D.edgeCarrier e) (hey : y ∈ D.edgeCarrier e) :
    D.BigCycle 2 where
  length_ge_two := by omega
  label := ![Sum.inl i, Sum.inr e]
  connector := ![Sum.inl x, Sum.inl y]
  adjacent_ne := by
    intro k
    fin_cases k <;> simp [cyclicSucc]
  connector_injective := by
    intro k l heq
    fin_cases k <;> fin_cases l <;>
      simp_all
  left_incident := by
    intro k
    fin_cases k
    · exact hix
    · exact hey
  right_incident := by
    intro k
    fin_cases k
    · simpa [cyclicSucc, Incident, carrier] using hex
    · simpa [cyclicSucc, Incident, carrier] using hiy

/-- Both boundary connectors are vertices, so both occurrences are
pure and the big-cycle order is exactly two. -/
theorem twoVertexEdgeProbe_twiceOrder
    (i : I) (e : E) (x y : V)
    (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hex : x ∈ D.edgeCarrier e) (hey : y ∈ D.edgeCarrier e) :
    (D.twoVertexEdgeProbe i e x y hxy hix hiy hex hey).twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, connectorKind, twoVertexEdgeProbe,
    Fin.sum_univ_two, cyclicSucc, twiceOccurrenceWeight]

/-- The probe satisfies literal (A1)--(A3), independently of
linearity and of the shape of the incident edge. -/
theorem twoVertexEdgeProbe_acceptable
    (i : I) (e : E) (x y : V)
    (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hex : x ∈ D.edgeCarrier e) (hey : y ∈ D.edgeCarrier e) :
    (D.twoVertexEdgeProbe i e x y hxy hix hiy hex hey).Acceptable := by
  let C := D.twoVertexEdgeProbe i e x y hxy hix hiy hex hey
  refine ⟨?_, D.twoCycle_A2 C, D.twoCycle_A3 C⟩
  intro ht
  have hfour : C.twiceOrder = 4 :=
    D.twoVertexEdgeProbe_twiceOrder i e x y hxy hix hiy hex hey
  have heq : (4 : ℕ) = 2 := hfour.symm.trans ht
  exact False.elim ((by decide : (4 : ℕ) ≠ 2) heq)

/-- Under order-two system girth, a designated copy through x and y
gets a genuine local short or long piece when a physical edge joins
the same vertices; the other label in the probe is an edge label. -/
theorem copy_piece_of_incident_edge
    (h : D.LocalPieceSystemBound 2)
    (i : I) (e : E) (x y : V) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hex : x ∈ D.edgeCarrier e) (hey : y ∈ D.edgeCarrier e) :
    D.ShortPiece (.inl i) (.inl x) (.inl y) ∨
      D.LongPiece (.inl i) (.inl x) (.inl y) := by
  let C := D.twoVertexEdgeProbe i e x y hxy hix hiy hex hey
  have hAccept : C.Acceptable :=
    D.twoVertexEdgeProbe_acceptable i e x y hxy hix hiy hex hey
  have hOrder : C.twiceOrder ≤ 2 * 2 := by
    rw [D.twoVertexEdgeProbe_twiceOrder i e x y hxy hix hiy hex hey]
  obtain ⟨k, hk, hPieces⟩ := h 2 C hAccept hOrder
  fin_cases k
  · have hne : C.label 1 ≠ C.label 0 := by
      simp [C, twoVertexEdgeProbe]
    have hp := hPieces 1 hne
    simpa [C, twoVertexEdgeProbe, trainCyclicPred] using hp
  · have hFalse : False := by
      simpa [C, twoVertexEdgeProbe, designated] using hk
    exact False.elim hFalse

/-- Short-piece case of the two-copy symmetry argument: the edge
supplied by the other designated copy is a physical probe which
forces a piece in the first copy as well. -/
theorem copy_piece_of_other_short
    (h : D.LocalPieceSystemBound 2)
    (i j : I) (x y : V) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hShort : D.ShortPiece (.inl j) (.inl x) (.inl y)) :
    D.ShortPiece (.inl i) (.inl x) (.inl y) ∨
      D.LongPiece (.inl i) (.inl x) (.inl y) := by
  rcases hShort with ⟨e, _he, hx, hy⟩
  exact D.copy_piece_of_incident_edge h i e x y hxy
    hix hiy hx hy

end StructuralRamsey.Girth.OrderOneData

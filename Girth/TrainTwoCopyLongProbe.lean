import Girth.TrainTwoCopyVertexProbe
import Mathlib.Tactic

/-!
# Circulation: probe a long two-copy witness by an order-two big cycle

Suppose a copy B supplies a legal long piece e₁⁺ W e₂⁺ between
distinct vertices x,y, with no ambient edge through the pair.
The cycle A x e₁⁺ W e₂⁺ y has one designated label A, has order
two, and satisfies A1--A3. Its supreme copy must be A, whose two
short mixed pieces yield edges in W incident to x and y. They are
distinct because no ambient edge contains both vertices.

Thus a long witness in B forces a legitimate long piece in A.
This completes the LOCAL-piece part of the circulation two-copy
symmetry proof; the simultaneous-global collapse back to the
original two-copy cycle is a separate verification step.
No appendix statements are used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Three-occurrence probe A x e⁺ W f⁺ y, made of a designated copy
and two actual, distinct edge labels of the same wagon. -/
def twoVertexLongProbe
    (i : I) (e f : E) (w : P) (x y : V)
    (hef : e ≠ f) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hew : D.parent e = w) (hfw : D.parent f = w)
    (hxe : x ∈ D.edgeCarrier e) (hyf : y ∈ D.edgeCarrier f)
    (hNonedge : ¬ D.PairEdge x y) :
    D.BigCycle 3 where
  length_ge_two := by omega
  label := ![Sum.inl i, Sum.inr e, Sum.inr f]
  connector := ![Sum.inl x, Sum.inr w, Sum.inl y]
  adjacent_ne := by
    intro k
    fin_cases k
    · simp [cyclicSucc]
    · simpa [cyclicSucc] using
        (fun h : (Sum.inr e : I ⊕ E) = Sum.inr f =>
          hef (Sum.inr.inj h))
    · simp [cyclicSucc]
  connector_injective := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all
  left_incident := by
    intro k
    fin_cases k
    · exact hix
    · exact ⟨e, rfl, hew⟩
    · exact hyf
  right_incident := by
    intro k
    fin_cases k
    · exact hxe
    · exact ⟨f, rfl, hfw⟩
    · exact hiy

/-- The connector types vertex/wagon/vertex give weights
1+1+2, so the cycle has order two. -/
theorem twoVertexLongProbe_twiceOrder
    (i : I) (e f : E) (w : P) (x y : V)
    (hef : e ≠ f) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hew : D.parent e = w) (hfw : D.parent f = w)
    (hxe : x ∈ D.edgeCarrier e) (hyf : y ∈ D.edgeCarrier f)
    (hNonedge : ¬ D.PairEdge x y) :
    (D.twoVertexLongProbe i e f w x y hef hxy hix hiy
      hew hfw hxe hyf hNonedge).twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, connectorKind, twoVertexLongProbe,
    Fin.sum_univ_three, cyclicSucc, twiceOccurrenceWeight]

/-- Exact acceptability A1--A3 of the long probe. The only A2
nonedge obligation is the original long piece's boundary guard. -/
theorem twoVertexLongProbe_acceptable
    (i : I) (e f : E) (w : P) (x y : V)
    (hef : e ≠ f) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hew : D.parent e = w) (hfw : D.parent f = w)
    (hxe : x ∈ D.edgeCarrier e) (hyf : y ∈ D.edgeCarrier f)
    (hNonedge : ¬ D.PairEdge x y) :
    (D.twoVertexLongProbe i e f w x y hef hxy hix hiy
      hew hfw hxe hyf hNonedge).Acceptable := by
  let C := D.twoVertexLongProbe i e f w x y hef hxy hix hiy
    hew hfw hxe hyf hNonedge
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    have hfour : C.twiceOrder = 4 :=
      D.twoVertexLongProbe_twiceOrder i e f w x y
        hef hxy hix hiy hew hfw hxe hyf hNonedge
    have hEq : (4 : ℕ) = 2 := hfour.symm.trans ht
    exact False.elim ((by decide : (4 : ℕ) ≠ 2) hEq)
  · constructor
    · intro k p hk j hj
      fin_cases k
      · simp [C, twoVertexLongProbe] at hk
      · fin_cases j
        · exact Or.inl (by decide)
        · rcases hj with ⟨z, hz, _⟩
          simp [C, twoVertexLongProbe] at hz
        · exact Or.inr (by decide)
      · simp [C, twoVertexLongProbe] at hk
    · intro k p vx vy hk hl hr _ _ _
      fin_cases k
      · simp [C, twoVertexLongProbe] at hk
      · have hx : vx = x := by
          simpa [C, twoVertexLongProbe, trainCyclicPred]
            using hl.symm
        have hy : vy = y := by
          simpa [C, twoVertexLongProbe, cyclicSucc]
            using hr.symm
        subst vx
        subst vy
        exact hNonedge
      · simp [C, twoVertexLongProbe] at hk
  · intro p _
    refine ⟨(2 : Fin 3), ?_⟩
    intro j hj
    fin_cases j
    · exact Or.inr (by decide)
    · rcases hj with ⟨z, hz, _⟩
      simp [C, twoVertexLongProbe] at hz
    · exact Or.inl rfl

/-- Given a legal long edge-pair probe, full order-two local
supremeness forces A to supply two actual edges in W through
x and y; since no edge contains x,y, they form a long piece. -/
theorem copy_long_piece_of_two_edge_probe
    (h : D.LocalPieceSystemBound 2)
    (i : I) (e f : E) (w : P) (x y : V)
    (hef : e ≠ f) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hew : D.parent e = w) (hfw : D.parent f = w)
    (hxe : x ∈ D.edgeCarrier e) (hyf : y ∈ D.edgeCarrier f)
    (hNonedge : ¬ D.PairEdge x y) :
    D.LongPiece (.inl i) (.inl x) (.inl y) := by
  let C := D.twoVertexLongProbe i e f w x y hef hxy hix hiy
    hew hfw hxe hyf hNonedge
  have hAcc : C.Acceptable :=
    D.twoVertexLongProbe_acceptable i e f w x y
      hef hxy hix hiy hew hfw hxe hyf hNonedge
  have hOrd : C.twiceOrder ≤ 2 * 2 := by
    rw [D.twoVertexLongProbe_twiceOrder i e f w x y
      hef hxy hix hiy hew hfw hxe hyf hNonedge]
  obtain ⟨k, hk, hp⟩ := h 3 C hAcc hOrd
  fin_cases k
  · have hne1 : C.label 1 ≠ C.label 0 := by
      simp [C, twoVertexLongProbe]
    have hne2 : C.label 2 ≠ C.label 0 := by
      simp [C, twoVertexLongProbe]
    have piece1 := hp 1 hne1
    have piece2 := hp 2 hne2
    have hBridge1 : D.Bridge (.inl i) x w := by
      exact D.piece_mixed_bridge (.inl i) x w
        (by simpa [C, twoVertexLongProbe, trainCyclicPred]
          using piece1)
    have hBridge2 : D.Bridge (.inl i) y w := by
      exact D.piece_mixed_bridge_reverse (.inl i) y w
        (by simpa [C, twoVertexLongProbe, trainCyclicPred]
          using piece2)
    rcases hBridge1 with ⟨a, ha, hwa, hxa⟩
    rcases hBridge2 with ⟨b, hb, hwb, hyb⟩
    have hne : a ≠ b := by
      intro eq
      subst b
      exact hNonedge ⟨a, hxa, hyb⟩
    exact ⟨x, y, w, a, b, rfl, rfl, ha, hb,
      hne, hwa, hwb, hxa, hyb, hNonedge⟩
  · have hFalse : False := by
      simpa [C, twoVertexLongProbe, designated] using hk
    exact False.elim hFalse
  · have hFalse : False := by
      simpa [C, twoVertexLongProbe, designated] using hk
    exact False.elim hFalse

/-- The long-witness case of local two-copy symmetry: a legal long
piece from B forces a long piece from A through the same vertices. -/
theorem copy_long_piece_of_other_long
    (h : D.LocalPieceSystemBound 2)
    (i j : I) (x y : V) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hLong : D.LongPiece (.inl j) (.inl x) (.inl y)) :
    D.LongPiece (.inl i) (.inl x) (.inl y) := by
  rcases hLong with ⟨x', y', w, e, f, hx', hy', he, hf,
    hef, hew, hfw, hxe, hyf, hNonedge⟩
  have hxx : x' = x := (Sum.inl.inj hx').symm
  have hyy : y' = y := (Sum.inl.inj hy').symm
  subst x'
  subst y'
  exact D.copy_long_piece_of_two_edge_probe h i e f w x y
    hef hxy hix hiy hew hfw hxe hyf hNonedge

end StructuralRamsey.Girth.OrderOneData

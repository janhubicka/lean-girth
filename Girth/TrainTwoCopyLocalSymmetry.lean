import Girth.TrainTwoCopyLongProbe

/-!
# Circulation: local two-copy symmetry at order two

We prove the complete LOCAL-piece consequence of the manuscript's
two-copy symmetry lemma. Two distinct designated copies A,B sharing
distinct vertices x,y form an acceptable two-occurrence cycle A x B y.
The system bound supplies a short or long piece in one of them.
The checked short-edge and long-edge probes then force a corresponding
piece in the other. Reverse endpoint orientation when the first
supreme label is the second occurrence.

The result does not yet assert that the two respective simultaneous
collapse words of the original cycle are globally legal. That is
handled by a separate finite-word verification step.

Only the circulation manuscript is formalized; no appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Reversing two vertex endpoints exchanges short-piece boundaries.
For a long piece it swaps both source edges and preserves the
no-common-ambient-edge guard. -/
theorem piece_vertices_reverse
    (a : I ⊕ E) (x y : V)
    (h : D.ShortPiece a (.inl x) (.inl y) ∨
      D.LongPiece a (.inl x) (.inl y)) :
    D.ShortPiece a (.inl y) (.inl x) ∨
      D.LongPiece a (.inl y) (.inl x) := by
  rcases h with ⟨e, he, hx, hy⟩ |
      ⟨x', y', w, e, f, hx, hy, he, hf,
        hne, hew, hfw, hxe, hyf, hNonedge⟩
  · exact Or.inl ⟨e, he, hy, hx⟩
  · have hReverse : ¬ D.PairEdge y' x' := by
      rintro ⟨g, hyg, hxg⟩
      exact hNonedge ⟨g, hxg, hyg⟩
    exact Or.inr ⟨y', x', w, f, e, hy, hx,
      hf, he, hne.symm, hfw, hew, hyf, hxe, hReverse⟩

/-- Having either kind of witness piece in one designated copy
forces at least one kind of witness piece in any other copy
containing the same distinct pair of vertices. -/
theorem copy_piece_of_other_piece
    (h : D.LocalPieceSystemBound 2)
    (i j : I) (x y : V) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hOther : D.ShortPiece (.inl j) (.inl x) (.inl y) ∨
      D.LongPiece (.inl j) (.inl x) (.inl y)) :
    D.ShortPiece (.inl i) (.inl x) (.inl y) ∨
      D.LongPiece (.inl i) (.inl x) (.inl y) := by
  rcases hOther with hShort | hLong
  · exact D.copy_piece_of_other_short h i j x y hxy hix hiy hShort
  · exact Or.inr
      (D.copy_long_piece_of_other_long h i j x y hxy hix hiy hLong)

/-- The canonical two-designated-copy, two-vertex big cycle A x B y. -/
def twoVertexTwoCopyCycle
    (i j : I) (x y : V)
    (hij : i ≠ j) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hjx : x ∈ D.copyCarrier j) (hjy : y ∈ D.copyCarrier j) :
    D.BigCycle 2 where
  length_ge_two := by omega
  label := ![Sum.inl i, Sum.inl j]
  connector := ![Sum.inl x, Sum.inl y]
  adjacent_ne := by
    intro k
    fin_cases k
    · simpa [cyclicSucc] using
        (fun h : (Sum.inl i : I ⊕ E) = Sum.inl j =>
          hij (Sum.inl.inj h))
    · simpa [cyclicSucc] using
        (fun h : (Sum.inl j : I ⊕ E) = Sum.inl i =>
          hij (Sum.inl.inj h).symm)
  connector_injective := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all
  left_incident := by
    intro k
    fin_cases k
    · exact hix
    · exact hjy
  right_incident := by
    intro k
    fin_cases k
    · simpa [cyclicSucc, Incident, carrier] using hjx
    · simpa [cyclicSucc, Incident, carrier] using hiy

/-- Both designated occurrences are pure (vertex/vertex), so the
two-copy big cycle has order two. -/
theorem twoVertexTwoCopyCycle_twiceOrder
    (i j : I) (x y : V)
    (hij : i ≠ j) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hjx : x ∈ D.copyCarrier j) (hjy : y ∈ D.copyCarrier j) :
    (D.twoVertexTwoCopyCycle i j x y hij hxy hix hiy hjx hjy).twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, connectorKind, twoVertexTwoCopyCycle,
    Fin.sum_univ_two, cyclicSucc, twiceOccurrenceWeight]

/-- A1 is vacuous at order two; A2 and A3 are automatic for the
two positions of the two-copy vertex cycle. -/
theorem twoVertexTwoCopyCycle_acceptable
    (i j : I) (x y : V)
    (hij : i ≠ j) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hjx : x ∈ D.copyCarrier j) (hjy : y ∈ D.copyCarrier j) :
    (D.twoVertexTwoCopyCycle i j x y hij hxy hix hiy hjx hjy).Acceptable := by
  let C := D.twoVertexTwoCopyCycle i j x y hij hxy hix hiy hjx hjy
  refine ⟨?_, D.twoCycle_A2 C, D.twoCycle_A3 C⟩
  intro ht
  have hfour : C.twiceOrder = 4 :=
    D.twoVertexTwoCopyCycle_twiceOrder
      i j x y hij hxy hix hiy hjx hjy
  have hEq : (4 : ℕ) = 2 := hfour.symm.trans ht
  exact False.elim ((by decide : (4 : ℕ) ≠ 2) hEq)

/-- Under the order-two local consequence of full system girth,
BOTH distinct designated copies have valid short/long replacement
pieces with the same ordered boundary vertices. -/
theorem twoVertexTwoCopyCycle_both_local_pieces
    (h : D.LocalPieceSystemBound 2)
    (i j : I) (x y : V)
    (hij : i ≠ j) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hjx : x ∈ D.copyCarrier j) (hjy : y ∈ D.copyCarrier j) :
    (D.ShortPiece (.inl i) (.inl x) (.inl y) ∨
      D.LongPiece (.inl i) (.inl x) (.inl y)) ∧
    (D.ShortPiece (.inl j) (.inl x) (.inl y) ∨
      D.LongPiece (.inl j) (.inl x) (.inl y)) := by
  let C := D.twoVertexTwoCopyCycle i j x y hij hxy hix hiy hjx hjy
  have hAcc : C.Acceptable :=
    D.twoVertexTwoCopyCycle_acceptable
      i j x y hij hxy hix hiy hjx hjy
  have hOrd : C.twiceOrder ≤ 2 * 2 := by
    rw [D.twoVertexTwoCopyCycle_twiceOrder
      i j x y hij hxy hix hiy hjx hjy]
  obtain ⟨k, _hk, hPiece⟩ := h 2 C hAcc hOrd
  fin_cases k
  · have hne : C.label 1 ≠ C.label 0 := by
      intro hEq
      have hsum : (Sum.inl j : I ⊕ E) = Sum.inl i := by
        simpa [C, twoVertexTwoCopyCycle] using hEq
      have hji : j = i := Sum.inl.inj hsum
      exact hij hji.symm
    have hFirst :
        D.ShortPiece (.inl i) (.inl x) (.inl y) ∨
          D.LongPiece (.inl i) (.inl x) (.inl y) := by
      simpa [C, twoVertexTwoCopyCycle, trainCyclicPred] using hPiece 1 hne
    have hSecond :=
      D.copy_piece_of_other_piece h j i x y hxy hjx hjy hFirst
    exact ⟨hFirst, hSecond⟩
  · have hne : C.label 0 ≠ C.label 1 := by
      intro hEq
      have hsum : (Sum.inl i : I ⊕ E) = Sum.inl j := by
        simpa [C, twoVertexTwoCopyCycle] using hEq
      have hij' : i = j := Sum.inl.inj hsum
      exact hij hij'
    have hSecondReverse :
        D.ShortPiece (.inl j) (.inl y) (.inl x) ∨
          D.LongPiece (.inl j) (.inl y) (.inl x) := by
      simpa [C, twoVertexTwoCopyCycle, trainCyclicPred] using hPiece 0 hne
    have hSecond :=
      D.piece_vertices_reverse (.inl j) y x hSecondReverse
    have hFirst :=
      D.copy_piece_of_other_piece h i j x y hxy hix hiy hSecond
    exact ⟨hFirst, hSecond⟩

end StructuralRamsey.Girth.OrderOneData

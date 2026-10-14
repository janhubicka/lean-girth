import Girth.TrainTwoCopyGlobalSecond

/-!
# Circulation: complete indexed two-copy symmetry

Local pieces in the two designated copies are already forced by the
order-two supreme-cycle bound. Each local piece yields a genuinely legal
global simultaneous replacement word, but the original existential
HasSimultaneousSupreme proposition forgets WHICH copy is kept.

By retaining the indices in HasSupremeAt we can now finish the precise
two-copy symmetry lemma of the circulation manuscript: both positions
of A x B y are supreme in the strong, simultaneous-global sense.
The proof uses neither the appendix nor a new geometric assumption.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- In the acceptable cycle A x B y (A and B different, x and y
different), the order-two global supreme-cycle bound supplies a
globally legal simultaneous plan retaining A AND another retaining B.
This is stronger than one unindexed `HasSimultaneousSupreme`. -/
theorem twoVertexTwoCopyCycle_both_indexed_supreme
    (h : D.SupremeCycleBound 2)
    (i j : I) (x y : V) (hij : i ≠ j) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hjx : x ∈ D.copyCarrier j) (hjy : y ∈ D.copyCarrier j) :
    (D.twoVertexTwoCopyCycle i j x y hij hxy hix hiy hjx hjy).HasSupremeAt
      D (0 : Fin 2) ∧
    (D.twoVertexTwoCopyCycle i j x y hij hxy hix hiy hjx hjy).HasSupremeAt
      D (1 : Fin 2) := by
  have hLocal : D.LocalPieceSystemBound 2 :=
    D.localPieceSystemBound_of_supremeCycleBound 2 h
  obtain ⟨hFirst, hSecond⟩ :=
    D.twoVertexTwoCopyCycle_both_local_pieces hLocal
      i j x y hij hxy hix hiy hjx hjy
  constructor
  · exact D.twoVertexTwoCopyCycle_first_supreme_of_piece
      i j x y hij hxy hix hiy hjx hjy hFirst
  · exact D.twoVertexTwoCopyCycle_second_supreme_of_reversed_piece
      i j x y hij hxy hix hiy hjx hjy
        (D.piece_vertices_reverse (.inl j) x y hSecond)

/-- The exact manuscript hypothesis includes physical linearity.
The symmetry argument itself only needs the supreme-cycle bound. -/
theorem twoVertexTwoCopyCycle_both_indexed_of_fullSystemGirth
    (h : D.FullSystemGirthGT 2)
    (i j : I) (x y : V) (hij : i ≠ j) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hjx : x ∈ D.copyCarrier j) (hjy : y ∈ D.copyCarrier j) :
    (D.twoVertexTwoCopyCycle i j x y hij hxy hix hiy hjx hjy).HasSupremeAt
      D (0 : Fin 2) ∧
    (D.twoVertexTwoCopyCycle i j x y hij hxy hix hiy hjx hjy).HasSupremeAt
      D (1 : Fin 2) :=
  D.twoVertexTwoCopyCycle_both_indexed_supreme h.2
    i j x y hij hxy hix hiy hjx hjy

end StructuralRamsey.Girth.OrderOneData

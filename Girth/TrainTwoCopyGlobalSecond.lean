import Girth.TrainTwoCopyGlobalFirst

/-!
# Circulation: the opposite orientation of the two-copy collapse

A short or long piece from the SECOND copy is inserted into the FIRST
occurrence of A x B y. The resulting word starts with the replacing edge;
it is the cyclic rotation of the one-copy edge or long-edge probe. We
construct this rotation as a genuine BigCycle, so global legality is
checked rather than assumed.

This is deliberately separate from the local-piece symmetry statement.
Only the circulation proof; no appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Edge x B y: a cyclically rotated version of the short probe
B y edge x. The edge joins both boundary vertices. -/
def twoVertexEdgeProbeRotated
    (j : I) (e : E) (x y : V)
    (hxy : x ≠ y)
    (hjx : x ∈ D.copyCarrier j) (hjy : y ∈ D.copyCarrier j)
    (hxe : x ∈ D.edgeCarrier e) (hye : y ∈ D.edgeCarrier e) :
    D.BigCycle 2 where
  length_ge_two := by omega
  label := ![Sum.inr e, Sum.inl j]
  connector := ![Sum.inl x, Sum.inl y]
  adjacent_ne := by
    intro k
    fin_cases k <;> simp [cyclicSucc]
  connector_injective := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all
  left_incident := by
    intro k
    fin_cases k
    · exact hxe
    · exact hjy
  right_incident := by
    intro k
    fin_cases k
    · simpa [cyclicSucc, Incident, carrier] using hjx
    · simpa [cyclicSucc, Incident, carrier] using hye

/-- e W f x B y: a cyclically rotated long probe. The first edge
meets y, the last source edge meets x, and both lie in W. -/
def twoVertexLongProbeRotated
    (j : I) (e f : E) (w : P) (x y : V)
    (hef : e ≠ f) (hxy : x ≠ y)
    (hjx : x ∈ D.copyCarrier j) (hjy : y ∈ D.copyCarrier j)
    (hew : D.parent e = w) (hfw : D.parent f = w)
    (hye : y ∈ D.edgeCarrier e) (hxf : x ∈ D.edgeCarrier f) :
    D.BigCycle 3 where
  length_ge_two := by omega
  label := ![Sum.inr e, Sum.inr f, Sum.inl j]
  connector := ![Sum.inr w, Sum.inl x, Sum.inl y]
  adjacent_ne := by
    intro k
    fin_cases k
    · simpa [cyclicSucc] using
        (fun h : (Sum.inr e : I ⊕ E) = Sum.inr f =>
          hef (Sum.inr.inj h))
    · simp [cyclicSucc]
    · simp [cyclicSucc]
  connector_injective := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all
  left_incident := by
    intro k
    fin_cases k
    · exact ⟨e, rfl, hew⟩
    · exact hxf
    · exact hjy
  right_incident := by
    intro k
    fin_cases k
    · exact ⟨f, rfl, hfw⟩
    · simpa [cyclicSucc, Incident, carrier] using hjx
    · simpa [cyclicSucc, Incident, carrier] using hye

/-- A local piece for the second label with the reversed boundary
orientation gives a globally valid simultaneous plan on the ORIGINAL
two-copy cycle, with the second occurrence kept. -/
theorem twoVertexTwoCopyCycle_second_supreme_of_reversed_piece
    (i j : I) (x y : V) (hij : i ≠ j) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hjx : x ∈ D.copyCarrier j) (hjy : y ∈ D.copyCarrier j)
    (hPiece :
      D.ShortPiece (.inl j) (.inl y) (.inl x) ∨
      D.LongPiece (.inl j) (.inl y) (.inl x)) :
    (D.twoVertexTwoCopyCycle i j x y hij hxy hix hiy hjx hjy).HasSimultaneousSupreme := by
  let C := D.twoVertexTwoCopyCycle i j x y hij hxy hix hiy hjx hjy
  rcases hPiece with ⟨e, he, hye, hxe⟩ |
      ⟨yy, xx, w, e, f, hy, hx, he, hf, hne,
        hew, hfw, hye, hxf, hNonedge⟩
  · have hxe' : x ∈ D.edgeCarrier e := by
      simpa [Incident, carrier] using hxe
    have hye' : y ∈ D.edgeCarrier e := by
      simpa [Incident, carrier] using hye
    let pieces : Fin 2 → TrainSupremePiece E P := ![.short e, .keep]
    refine ⟨(1 : Fin 2), ?_, pieces, ?_, ?_⟩
    · simp [C, twoVertexTwoCopyCycle, designated]
    · intro k
      fin_cases k
      · constructor
        · intro heq
          have hlabels : C.label 0 ≠ C.label 1 := by
            simpa [C, twoVertexTwoCopyCycle] using hij
          exact False.elim (hlabels heq)
        · intro _
          simpa [pieces, BigCycle.ShortValid, C,
            twoVertexTwoCopyCycle, trainCyclicPred,
            Incident, carrier] using
              (show e ∈ D.edges (.inl j) ∧
                y ∈ D.edgeCarrier e ∧ x ∈ D.edgeCarrier e from
                ⟨he, hye', hxe'⟩)
      · constructor
        · intro _
          rfl
        · intro hne'
          exact False.elim (hne' rfl)
    · refine ⟨2,
        D.twoVertexEdgeProbeRotated j e x y hxy hjx hjy hxe' hye', ?_⟩
      simp [BigCycle.resultWord, BigCycle.pieceWord, pieces,
        C, twoVertexTwoCopyCycle, twoVertexEdgeProbeRotated,
        List.ofFn, Fin.foldr_succ, Fin.foldr_zero]
  · have hyy : yy = y := (Sum.inl.inj hy).symm
    have hxx : xx = x := (Sum.inl.inj hx).symm
    subst yy
    subst xx
    let pieces : Fin 2 → TrainSupremePiece E P :=
      ![.long e w f, .keep]
    refine ⟨(1 : Fin 2), ?_, pieces, ?_, ?_⟩
    · simp [C, twoVertexTwoCopyCycle, designated]
    · intro k
      fin_cases k
      · constructor
        · intro heq
          have hlabels : C.label 0 ≠ C.label 1 := by
            simpa [C, twoVertexTwoCopyCycle] using hij
          exact False.elim (hlabels heq)
        · intro _
          simpa [pieces, BigCycle.LongValid, C,
            twoVertexTwoCopyCycle, trainCyclicPred] using
              (show ∃ (a b : V), a = y ∧ b = x ∧
                e ∈ D.edges (.inl j) ∧ f ∈ D.edges (.inl j) ∧
                e ≠ f ∧ D.parent e = w ∧ D.parent f = w ∧
                a ∈ D.edgeCarrier e ∧ b ∈ D.edgeCarrier f ∧
                ¬ D.PairEdge a b from
                ⟨y, x, rfl, rfl, he, hf,
                  hne, hew, hfw, hye, hxf, hNonedge⟩)
      · constructor
        · intro _
          rfl
        · intro hne'
          exact False.elim (hne' rfl)
    · refine ⟨3,
        D.twoVertexLongProbeRotated j e f w x y hne hxy
          hjx hjy hew hfw hye hxf, ?_⟩
      simp [BigCycle.resultWord, BigCycle.pieceWord, pieces,
        C, twoVertexTwoCopyCycle, twoVertexLongProbeRotated,
        List.ofFn, Fin.foldr_succ, Fin.foldr_zero]

end StructuralRamsey.Girth.OrderOneData

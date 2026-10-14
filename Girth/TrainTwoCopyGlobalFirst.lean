import Girth.TrainTwoCopyLocalSymmetry
import Girth.TrainSimultaneousSupreme

/-!
# Circulation: a local piece really gives a global two-copy collapse

For a two-designated-copy cycle A x B y, any genuine short or long
piece belonging to A and joining x to y gives a simultaneous supreme
plan with A retained and B replaced. The resulting full cyclic word
is respectively A x e⁺ y or A x e⁺ W f⁺ y. Each is a genuine big
cycle: the types distinguish A from its actual edge labels, long
source edges are distinct, and the vertex endpoints are distinct.

This is the global finite-word step which local-piece symmetry alone
does not provide. The companion statement for retaining B instead
of A follows by cyclic rotation and is kept separate.

Only circulation arguments; no appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A valid short or long local piece of the FIRST designated copy
provides a globally legal simultaneous supreme collapse of the
original two-copy big cycle. -/
theorem twoVertexTwoCopyCycle_first_supreme_of_piece
    (i j : I) (x y : V) (hij : i ≠ j) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i) (hiy : y ∈ D.copyCarrier i)
    (hjx : x ∈ D.copyCarrier j) (hjy : y ∈ D.copyCarrier j)
    (hPiece :
      D.ShortPiece (.inl i) (.inl x) (.inl y) ∨
      D.LongPiece (.inl i) (.inl x) (.inl y)) :
    (D.twoVertexTwoCopyCycle i j x y hij hxy hix hiy hjx hjy).HasSimultaneousSupreme := by
  let C := D.twoVertexTwoCopyCycle i j x y hij hxy hix hiy hjx hjy
  rcases hPiece with ⟨e, he, hxe, hye⟩ |
      ⟨xx, yy, w, e, f, hx, hy, he, hf, hne,
        hew, hfw, hxe, hyf, hNonedge⟩
  · have hxe' : x ∈ D.edgeCarrier e := by
      simpa [Incident, carrier] using hxe
    have hye' : y ∈ D.edgeCarrier e := by
      simpa [Incident, carrier] using hye
    let pieces : Fin 2 → TrainSupremePiece E P := ![.keep, .short e]
    refine ⟨(0 : Fin 2), ?_, pieces, ?_, ?_⟩
    · simp [C, twoVertexTwoCopyCycle, designated]
    · intro k
      fin_cases k
      · constructor
        · intro _
          rfl
        · intro hne'
          exact False.elim (hne' rfl)
      · constructor
        · intro heq
          have hlabels : C.label 1 ≠ C.label 0 := by
            simp [C, twoVertexTwoCopyCycle, hij]
          exact False.elim (hlabels heq)
        · intro _
          simpa [pieces, BigCycle.ShortValid, C,
            twoVertexTwoCopyCycle, trainCyclicPred,
            Incident, carrier] using
              (show e ∈ D.edges (.inl i) ∧
                x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier e from
                ⟨he, hxe', hye'⟩)
    · refine ⟨2,
        D.twoVertexEdgeProbe i e x y hxy hix hiy hxe' hye', ?_⟩
      simp [BigCycle.resultWord, BigCycle.pieceWord, pieces,
        C, twoVertexTwoCopyCycle, twoVertexEdgeProbe, List.ofFn]
  · have hxx : xx = x := (Sum.inl.inj hx).symm
    have hyy : yy = y := (Sum.inl.inj hy).symm
    subst xx
    subst yy
    let pieces : Fin 2 → TrainSupremePiece E P :=
      ![.keep, .long e w f]
    refine ⟨(0 : Fin 2), ?_, pieces, ?_, ?_⟩
    · simp [C, twoVertexTwoCopyCycle, designated]
    · intro k
      fin_cases k
      · constructor
        · intro _
          rfl
        · intro hne'
          exact False.elim (hne' rfl)
      · constructor
        · intro heq
          have hlabels : C.label 1 ≠ C.label 0 := by
            simp [C, twoVertexTwoCopyCycle, hij]
          exact False.elim (hlabels heq)
        · intro _
          simpa [pieces, BigCycle.LongValid, C,
            twoVertexTwoCopyCycle, trainCyclicPred] using
              (show ∃ (a b : V), a = x ∧ b = y ∧
                e ∈ D.edges (.inl i) ∧ f ∈ D.edges (.inl i) ∧
                e ≠ f ∧ D.parent e = w ∧ D.parent f = w ∧
                a ∈ D.edgeCarrier e ∧ b ∈ D.edgeCarrier f ∧
                ¬ D.PairEdge a b from
                ⟨x, y, rfl, rfl, he, hf,
                  hne, hew, hfw, hxe, hyf, hNonedge⟩)
    · refine ⟨3,
        D.twoVertexLongProbe i e f w x y hne hxy
          hix hiy hew hfw hxe hyf hNonedge, ?_⟩
      simp [BigCycle.resultWord, BigCycle.pieceWord, pieces,
        C, twoVertexTwoCopyCycle, twoVertexLongProbe, List.ofFn]

end StructuralRamsey.Girth.OrderOneData

import Girth.TrainFirstLongNeighbours
import Girth.TrainComposeLongBridges

/-!
# Circulation: lift the two later short pieces of a first long block

The checked neighbour equations for a first long replacement show
that its fresh output wagon has exactly the old source boundaries
as its two neighbours. Later short pieces on both sides therefore
give two bridges from the selected supreme target through the same
wagon. The original nonedge condition makes the edges distinct and
produces a genuine LongValid source piece.

This handles the hard LOCAL composition case for arbitrary first
long replacements. Global witness selection/assembly remains separate.
No appendix theorem is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

theorem BigCycle.compose_first_long_from_two_later_shorts
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (first : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry D first)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      first i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D first)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (kC : Fin n) (kB : Fin m)
    (hTarget : B.label kB = C.label kC)
    (i : Fin n) (e f : E) (p : P)
    (hPiece : first i = .long e p f)
    (j : Fin m) (hj : B.connector j = Sum.inr p)
    (g h : E)
    (hFirst : B.ShortValid D kB j g)
    (hSecond : B.ShortValid D kB (oldPos i) h) :
    ∃ a b : E, C.LongValid D kC i a p b := by
  obtain ⟨x, y, hCx, hCy, _hPx, _hPy, hNonedge⟩ :=
    hGeom i e f p hPiece
  obtain ⟨hPrevPos, hNextPos⟩ :=
    C.literal_long_fresh_neighbours D B first hFresh
      hWord oldPos hConnector i e f p hPiece j hj
  have hBLeft : B.connector (trainCyclicPred j) = Sum.inl x := by
    calc
      B.connector (trainCyclicPred j) =
          B.connector (oldPos (trainCyclicPred i)) :=
            congrArg B.connector hPrevPos.symm
      _ = C.connector (trainCyclicPred i) := hConnector _
      _ = Sum.inl x := hCx
  have hBRight : B.connector (oldPos i) = Sum.inl y :=
    (hConnector i).trans hCy
  have hRightPred : trainCyclicPred (oldPos i) = j := by
    have heq := congrArg trainCyclicPred hNextPos
    simpa [trainCyclicPred_cyclicSucc_of_two_le B.length_ge_two j]
      using heq
  obtain ⟨hg, hgx, hgp⟩ := hFirst
  obtain ⟨hh, hhp, hhy⟩ := hSecond
  have hLeftPiece :
      D.ShortPiece (C.label kC) (Sum.inl x) (Sum.inr p) := by
    refine ⟨g, ?_, ?_, ?_⟩
    · simpa only [hTarget] using hg
    · simpa only [hBLeft] using hgx
    · simpa only [hj] using hgp
  have hRightPiece :
      D.ShortPiece (C.label kC) (Sum.inr p) (Sum.inl y) := by
    refine ⟨h, ?_, ?_, ?_⟩
    · simpa only [hTarget] using hh
    · simpa only [hRightPred, hj] using hhp
    · simpa only [hBRight] using hhy
  have hb1 : D.Bridge (C.label kC) x p :=
    D.piece_mixed_bridge (C.label kC) x p (Or.inl hLeftPiece)
  have hb2 : D.Bridge (C.label kC) y p :=
    D.piece_mixed_bridge_reverse (C.label kC) y p (Or.inl hRightPiece)
  exact C.exists_longValid_of_two_bridges D kC i x y p
    hCx hCy hb1 hb2 hNonedge

end StructuralRamsey.Girth.OrderOneData

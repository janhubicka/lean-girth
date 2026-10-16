import Girth.TrainThreeWagonCycleAcceptability
import Girth.TrainTwoOccurrenceMixedLong
import Mathlib.Tactic

/-!
# Circulation: acceptability and order for actual two-to-three long expansions

When an original two-occurrence cycle has one retained designated label
and the other occurrence is a long piece, the actual flattened output word
has length three and exactly one wagon connector.

The earlier verified literal-word constructions (#532) guarantee this
is a genuine BigCycle; #533 verifies A1--A3 and numerical order for both
possible orientations.  We connect these facts to the literal
PlanValid/resultWord interface, rather than introducing an unrelated
abstract three-cycle.

There is no appeal to output wagon linearity, general admissible
replacement, or the appendix. The general long-insertion A2/A3 argument
for sources of length >= 3 remains separate.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- If occurrence zero is kept and occurrence one is long, EVERY actual
three-occurrence output cycle with the literal replacement word is
acceptable and has exactly the original order. -/
theorem BigCycle.two_keep0_long1_output_accept_order
    (C : D.BigCycle 2) (B : D.BigCycle 3)
    (pieces : Fin 2 → TrainSupremePiece E P)
    (hKeep : pieces 0 = .keep)
    (e f : E) (w : P)
    (hLong : pieces 1 = .long e w f)
    (hValid : C.LongValid D 0 1 e w f)
    (hWord : List.ofFn (fun i : Fin 3 =>
      (B.label i, B.connector i)) = C.resultWord D pieces) :
    B.Acceptable ∧ B.twiceOrder = C.twiceOrder := by
  obtain ⟨x, y, hPrev, hHere, _he, _hf, _hef, _hew,
    _hfw, _hxe, _hyf, hNoPair⟩ := hValid
  have hx : C.connector 0 = Sum.inl x := by
    simpa [trainCyclicPred] using hPrev
  have hy : C.connector 1 = Sum.inl y := hHere
  have hw :
      [(B.label 0, B.connector 0),
       (B.label 1, B.connector 1),
       (B.label 2, B.connector 2)] =
      [(C.label 0, C.connector 0),
       (Sum.inr e, Sum.inr w),
       (Sum.inr f, C.connector 1)] := by
    simpa [BigCycle.resultWord, BigCycle.pieceWord,
      hKeep, hLong, List.ofFn_succ, List.ofFn_zero] using hWord
  have hc0 : B.connector 0 = C.connector 0 :=
    congrArg Prod.snd (List.cons.inj hw).1
  have hc1 : B.connector 1 = Sum.inr w :=
    congrArg Prod.snd (List.cons.inj (List.cons.inj hw).2).1
  have hc2 : B.connector 2 = C.connector 1 :=
    congrArg Prod.snd (List.cons.inj (List.cons.inj (List.cons.inj hw).2).2).1
  have hb0 : B.connector 0 = Sum.inl x := hc0.trans hx
  have hb2 : B.connector 2 = Sum.inl y := hc2.trans hy
  have hAcc := B.three_vwv_acceptable D x y w hb0 hc1 hb2 hNoPair
  have hOrdC := C.two_vertices_twiceOrder D x y hx hy
  have hOrdB := B.three_vwv_twiceOrder D x y w hb0 hc1 hb2
  exact ⟨hAcc, hOrdB.trans hOrdC.symm⟩

/-- Symmetric version when occurrence one is kept and occurrence zero
is long. Again the output is the ACTUAL replacement word, not merely
an abstract cyclic rotation. -/
theorem BigCycle.two_long0_keep1_output_accept_order
    (C : D.BigCycle 2) (B : D.BigCycle 3)
    (pieces : Fin 2 → TrainSupremePiece E P)
    (hKeep : pieces 1 = .keep)
    (e f : E) (w : P)
    (hLong : pieces 0 = .long e w f)
    (hValid : C.LongValid D 1 0 e w f)
    (hWord : List.ofFn (fun i : Fin 3 =>
      (B.label i, B.connector i)) = C.resultWord D pieces) :
    B.Acceptable ∧ B.twiceOrder = C.twiceOrder := by
  obtain ⟨x, y, hPrev, hHere, _he, _hf, _hef, _hew,
    _hfw, _hxe, _hyf, hNoPair⟩ := hValid
  have hx : C.connector 1 = Sum.inl x := by
    simpa [trainCyclicPred] using hPrev
  have hy : C.connector 0 = Sum.inl y := hHere
  have hw :
      [(B.label 0, B.connector 0),
       (B.label 1, B.connector 1),
       (B.label 2, B.connector 2)] =
      [(Sum.inr e, Sum.inr w),
       (Sum.inr f, C.connector 0),
       (C.label 1, C.connector 1)] := by
    simpa [BigCycle.resultWord, BigCycle.pieceWord,
      hKeep, hLong, List.ofFn_succ, List.ofFn_zero] using hWord
  have hc0 : B.connector 0 = Sum.inr w :=
    congrArg Prod.snd (List.cons.inj hw).1
  have hc1 : B.connector 1 = C.connector 0 :=
    congrArg Prod.snd (List.cons.inj (List.cons.inj hw).2).1
  have hc2 : B.connector 2 = C.connector 1 :=
    congrArg Prod.snd (List.cons.inj (List.cons.inj (List.cons.inj hw).2).2).1
  have hb1 : B.connector 1 = Sum.inl y := hc1.trans hy
  have hb2 : B.connector 2 = Sum.inl x := hc2.trans hx
  have hAcc := B.three_wvv_acceptable D x y w hc0 hb1 hb2 hNoPair
  have hOrdC := C.two_vertices_twiceOrder D y x hy hx
  have hOrdB := B.three_wvv_twiceOrder D x y w hc0 hb1 hb2
  exact ⟨hAcc, hOrdB.trans hOrdC.symm⟩

end StructuralRamsey.Girth.OrderOneData

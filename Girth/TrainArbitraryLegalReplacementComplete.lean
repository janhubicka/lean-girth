import Girth.TrainArbitrarySupremeComposition
import Girth.TrainArbitraryLiteralA2
import Girth.TrainOptionalFreshnessConverse

/-!
# Circulation: the complete admissible replacement theorem for a legal output

The manuscript's admissible-replacement lemma has three claims:
1. the resulting cycle is acceptable,
2. it has the original numerical order,
3. every supreme label of the output is supreme in the source.

All three hold for arbitrary simultaneous locally valid replacement
pieces as soon as their literal word is already a legal BigCycle.
A1 at order one requires retaining a designated occurrence.
In particular, no selected source supreme target or PlanValid is
assumed for the first replacement.

The separate automatic-legality assertion for source length >=3 is
proved using the intrinsic CyclicWordChecks. We deliberately do not
assume that statement here and use no appendix theorem.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- All three conclusions of admissible replacement, with the first
literal output already a legal BigCycle, at every source length. -/
theorem BigCycle.arbitrary_legal_replacement_all_conclusions
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces)
    (hRetain : C.twiceOrder = 2 →
      ∃ j : Fin m, D.designated (B.label j)) :
    B.Acceptable ∧
    B.twiceOrder = C.twiceOrder ∧
    (∀ kB : Fin m, B.HasSupremeAt D kB →
      ∃ kC : Fin n, C.label kC = B.label kB ∧
        C.HasSupremeAt D kC) := by
  have hFresh := C.longWagons_fresh_of_literalBigCycle
    D B pieces hWord
  obtain ⟨hOutputAccept, hOrder⟩ :=
    C.output_acceptable_order_of_arbitrary_geometry
      D B hAccept hLinear pieces hGeom hFresh hWord hRetain
  refine ⟨hOutputAccept, hOrder, ?_⟩
  intro kB hSupreme
  exact C.supreme_of_arbitrary_literal_replacement
    D B hAccept hLinear pieces hGeom hWord kB hSupreme

end StructuralRamsey.Girth.OrderOneData

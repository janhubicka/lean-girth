import Girth.TrainArbitraryWordAssembly
import Girth.TrainArbitraryLegalReplacementComplete
import Girth.TrainBigCycleOrderBudget

/-!
# Circulation: the complete admissible-replacement lemma at length >=3

Arbitrary locally chosen physical short/long replacements satisfying
the true incidence, wagon-boundary, nonedge and freshness conditions
produce a literal BigCycle automatically when the source is acceptable
and has at least three occurrences.

The checked legal-output admissible-replacement theorem then gives
acceptability, exact twice-order, and the lifting of EVERY later
supreme label back to the original source.

At source length >=3, the order-one designated-retention obligation
is vacuous because twiceOrder >= source length. This therefore
assembles all assertions of the published admissible-replacement
lemma, with no first-stage common selected supreme target and no
appendix input.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Arbitrary local geometric replacement, including automatic
BigCycle legality, preserves all relevant properties and supreme
labels at source length at least three. -/
theorem BigCycle.arbitrary_replacement_complete_of_three_le
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (hn : 3 ≤ n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hInc : C.LocalPieceIncidence D pieces)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    ∃ m : ℕ, ∃ B : D.BigCycle m,
      List.ofFn (fun j : Fin m =>
        (B.label j, B.connector j)) = C.resultWord D pieces ∧
      B.Acceptable ∧ B.twiceOrder = C.twiceOrder ∧
      (∀ kB : Fin m, B.HasSupremeAt D kB →
        ∃ kC : Fin n, C.label kC = B.label kB ∧
          C.HasSupremeAt D kC) := by
  obtain ⟨m, B, hWord⟩ :=
    C.arbitrary_planProducesBigCycle_of_localGeometry
      D hAccept hn pieces hInc hGeom hFresh
  have hRetain : C.twiceOrder = 2 →
      ∃ j : Fin m, D.designated (B.label j) := by
    intro hOrder
    have hBound := C.length_le_twiceOrder
    omega
  obtain ⟨hOutAccept, hOrder, hSupreme⟩ :=
    C.arbitrary_legal_replacement_all_conclusions
      D B hAccept hLinear pieces hGeom hWord hRetain
  exact ⟨m, B, hWord, hOutAccept, hOrder, hSupreme⟩

end StructuralRamsey.Girth.OrderOneData

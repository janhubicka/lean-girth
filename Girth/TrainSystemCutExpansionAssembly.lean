import Girth.TrainSystemCutWagonRetype
import Girth.TrainArbitraryReplacementComplete
import Mathlib.Tactic

/-!
# Reduce the system-girth-to-cut-girth converse to physical wagon choices

A chordless labelled cut cycle is already an acceptable temporary
designated-wagon BigCycle. If each of its temporary occurrences is
replaced by a genuine physical short or long piece, the checked
arbitrary-replacement theorem constructs a legal, acceptable output
with the exact same order. The retyping theorem transfers that output
to the ORIGINAL system, where it has only edge labels. This contradicts
FullSystemGirthGT.

This is a genuine noncircular assembly. It leaves two exact geometric
inputs open: a shortest labelled cycle has the no-chord window, and
every source wagon admits one of the physical pieces. The latter
must be proved from the actual wagon edges, not postulated in the
final result. No appendix is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A legal physical replacement choice for every temporary wagon
already contradicts the original full system-girth bound.

All source labels are temporary wagons, all output labels are true
physical edges. The complete word legality and A1--A3 acceptability
are inherited from the checked arbitrary-replacement API. -/
theorem false_of_chordless_wagon_cycle_and_physical_pieces
    (q : ℕ) (hFull : D.FullSystemGirthGT q)
    (C : LabelledBergeCycle (fun p : P => {x : V | D.WagonVertex p x}))
    (hn : 3 ≤ C.length) (hq : C.length ≤ q)
    (hChordless : ∀ p : P, ∃ i : Fin C.length,
      ∀ j : Fin C.length,
        D.WagonVertex p (C.vertex j) →
        j = i ∨ j = cyclicSucc i)
    (pieces : Fin C.length → TrainSupremePiece E P)
    (hNone : ∀ i : Fin C.length, pieces i ≠ .keep)
    (hInc : (C.toWagonSeedBigCycle D).LocalPieceIncidence
      (D.wagonSeed) pieces)
    (hGeom : (C.toWagonSeedBigCycle D).LocalLongA2Geometry
      (D.wagonSeed) pieces) : False := by
  let seed := C.toWagonSeedBigCycle D
  have hSeedAccept : seed.Acceptable :=
    C.wagonSeed_acceptable_of_chordless D hn hChordless
  have hSeedLinear : (D.wagonSeed).LinearPretrain :=
    (D.wagonSeed_linear_iff).2 hFull.1
  have hFresh :
      ∀ (i : Fin C.length) (e : E) (p : P) (f : E),
        pieces i = .long e p f →
        ∀ t : Fin C.length, seed.connector t ≠ Sum.inr p := by
    intro i e p f hp t
    change Sum.inl (C.vertex t) ≠ Sum.inr p
    intro impossible
    cases impossible
  obtain ⟨m, B, hWord, hAccept, hOrder, _⟩ :=
    seed.arbitrary_replacement_complete_of_three_le
      (D.wagonSeed) hSeedAccept hSeedLinear hn
      pieces hInc hGeom hFresh
  have hOnly : ∀ j : Fin m, ∃ e : E, B.label j = Sum.inr e :=
    seed.output_edgeOnly_of_no_keeps D pieces hNone B hWord
  let Out : D.BigCycle m := B.retypeWagonSeedEdgeOnly D hOnly
  have hNotOne : B.twiceOrder ≠ 2 := by
    rw [hOrder, C.wagonSeed_twiceOrder]
    omega
  have hOutAcc : Out.Acceptable :=
    B.retypeWagonSeedEdgeOnly_acceptable D hOnly hAccept hNotOne
  have hOutOrder : Out.twiceOrder ≤ 2 * q := by
    change (B.retypeWagonSeedEdgeOnly D hOnly).twiceOrder ≤ 2 * q
    rw [B.retypeWagonSeedEdgeOnly_twiceOrder D hOnly, hOrder,
      C.wagonSeed_twiceOrder D]
    omega
  exact Out.false_of_acceptable_edgeOnly_fullSystemGirth
    D q hFull hOutAcc hOutOrder
    (B.retypeWagonSeedEdgeOnly_only_edges D hOnly)

end StructuralRamsey.Girth.OrderOneData

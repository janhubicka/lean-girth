import Girth.TrainSystemCutPhysicalPieces
import Girth.TrainSystemCutAllWagonWindow
import Girth.TrainArbitraryReplacementComplete
import Mathlib.Tactic

/-!
# A shortest labelled wagon cycle gives a real edge-only BigCycle

The universal cut-girth converse was already checked by contradiction
with FullSystemGirthGT. The manuscript's edge-only correspondence is
stronger and conceptually cleaner if we also extract the ACTUAL
acceptable edge-only cycle before invoking any system-girth bound.

A shortest labelled wagon cycle has the complete no-chord contact
window under physical wagon linearity. Give each wagon a temporary
designated label, replace it by one genuine short edge or two genuine
long-piece edges, assemble the exact cyclic output word via the
already verified arbitrary-replacement lemma and retype ALL output
labels to physical edges of the ORIGINAL pretrain. No FullSystemGirthGT
premise is used. The twice-order is exactly twice the original
labelled cycle length, not merely bounded by it.

This completes the reverse existential construction needed to shorten
the circulation's edge-only/wagon-girth lemma; no appendix is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A labelled wagon cycle of length >=3 with an A3 contact window
expands to a TRUE acceptable edge-only BigCycle of exactly the same
numerical order, assuming only complete pretrain linearity. -/
theorem exists_acceptable_edgeOnly_of_chordless_wagon_cycle
    (hLinear : D.LinearPretrain)
    (C : LabelledBergeCycle (fun p : P => {x : V | D.WagonVertex p x}))
    (hn : 3 ≤ C.length)
    (hChordless : ∀ p : P, ∃ i : Fin C.length,
      ∀ j : Fin C.length,
        D.WagonVertex p (C.vertex j) →
        j = i ∨ j = cyclicSucc i) :
    ∃ m : ℕ, ∃ B : D.BigCycle m,
      B.Acceptable ∧ B.twiceOrder = 2 * C.length ∧
      (∀ i : Fin m, ∃ e : E, B.label i = Sum.inr e) := by
  obtain ⟨pieces, hNone, hInc, hGeom⟩ :=
    C.exists_physical_pieces D
  let seed := C.toWagonSeedBigCycle D
  have hSeedAccept : seed.Acceptable :=
    C.wagonSeed_acceptable_of_chordless D hn hChordless
  have hSeedLinear : (D.wagonSeed).LinearPretrain :=
    (D.wagonSeed_linear_iff).2 hLinear
  have hFresh : ∀ (j : Fin C.length) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin C.length, seed.connector t ≠ Sum.inr p := by
    intro j e p f hp t
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
  have hOutOrder : Out.twiceOrder = 2 * C.length := by
    change (B.retypeWagonSeedEdgeOnly D hOnly).twiceOrder = 2 * C.length
    rw [B.retypeWagonSeedEdgeOnly_twiceOrder D hOnly,
      hOrder, C.wagonSeed_twiceOrder D]
  exact ⟨m, Out, hOutAcc, hOutOrder,
    B.retypeWagonSeedEdgeOnly_only_edges D hOnly⟩

/-- A globally shortest labelled cycle in a linear wagon family
has the required contact window by the checked shortcut theorem.
The resulting edge-only physical big cycle is constructed
unconditionally; system girth is not assumed. -/
theorem exists_acceptable_edgeOnly_of_minimal_wagon_cycle
    (hLinear : D.LinearPretrain)
    (C : LabelledBergeCycle (fun p : P => {x : V | D.WagonVertex p x}))
    (hn : 3 ≤ C.length)
    (hMinimal : ∀ B : LabelledBergeCycle
      (fun p : P => {x : V | D.WagonVertex p x}),
      C.length ≤ B.length) :
    ∃ m : ℕ, ∃ B : D.BigCycle m,
      B.Acceptable ∧ B.twiceOrder = 2 * C.length ∧
      (∀ i : Fin m, ∃ e : E, B.label i = Sum.inr e) := by
  have hChordless :=
    C.contact_window_of_global_minimal
      (fun p : P => {x : V | D.WagonVertex p x})
      hMinimal hLinear.2 hn
  exact D.exists_acceptable_edgeOnly_of_chordless_wagon_cycle
    hLinear C hn hChordless

end StructuralRamsey.Girth.OrderOneData

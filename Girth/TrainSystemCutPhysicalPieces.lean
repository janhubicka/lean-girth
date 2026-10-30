import Girth.TrainSystemCutExpansionAssembly
import Mathlib.Tactic

/-!
# Actual short-or-long replacement pieces for every wagon boundary

For a labelled wagon cycle, the two boundary vertices of each wagon
are incident with genuine physical edges of that same wagon. If one
physical edge contains both vertices, choose a short replacement.
Otherwise choose the two boundary edges as a long replacement. Since
no ambient edge joins the pair, these two edges are distinct.

All choices preserve literal physical incidence and satisfy the
geometric A2 input required by the checked arbitrary-replacement
theorem. No ghost edge, assumed designated copy or made-up train
intersection is introduced.

This closes the physical-piece-selection input of the conditional
system-to-cut contradiction. Shortest-cycle chordlessness remains
independent and is NOT inferred here.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Genuine physical short/long pieces are available at EVERY wagon
of an arbitrary labelled cut cycle, without a shortestness hypothesis.
No auxiliary designated-wagon occurrence is kept. -/
theorem _root_.StructuralRamsey.Girth.LabelledBergeCycle.exists_physical_pieces
    (C : LabelledBergeCycle (fun p : P => {x : V | D.WagonVertex p x})) :
    ∃ pieces : Fin C.length → TrainSupremePiece E P,
      (∀ i : Fin C.length, pieces i ≠ .keep) ∧
      (C.toWagonSeedBigCycle D).LocalPieceIncidence
        (D.wagonSeed) pieces ∧
      (C.toWagonSeedBigCycle D).LocalLongA2Geometry
        (D.wagonSeed) pieces := by
  classical
  let Good (i : Fin C.length) : TrainSupremePiece E P → Prop
    | .keep => False
    | .short e =>
        C.vertex (trainCyclicPred i) ∈ D.edgeCarrier e ∧
          C.vertex i ∈ D.edgeCarrier e
    | .long e p f =>
        e ≠ f ∧ D.parent e = p ∧ D.parent f = p ∧
        C.vertex (trainCyclicPred i) ∈ D.edgeCarrier e ∧
        C.vertex i ∈ D.edgeCarrier f ∧
        D.WagonVertex p (C.vertex (trainCyclicPred i)) ∧
        D.WagonVertex p (C.vertex i) ∧
        ¬ D.PairEdge (C.vertex (trainCyclicPred i)) (C.vertex i)
  have existsGood : ∀ i : Fin C.length, ∃ piece, Good i piece := by
    intro i
    have hFirst : D.WagonVertex (C.label i)
        (C.vertex (trainCyclicPred i)) := by
      have h := C.right_mem (trainCyclicPred i)
      rw [cyclicSucc_trainCyclicPred_of_two_le C.hlength i] at h
      exact h
    have hLast : D.WagonVertex (C.label i) (C.vertex i) :=
      C.left_mem i
    by_cases hPair : D.PairEdge
        (C.vertex (trainCyclicPred i)) (C.vertex i)
    · obtain ⟨e, hxe, hye⟩ := hPair
      exact ⟨.short e, ⟨hxe, hye⟩⟩
    · obtain ⟨e, he, hxe⟩ := hFirst
      obtain ⟨f, hf, hyf⟩ := hLast
      have hne : e ≠ f := by
        intro heq
        apply hPair
        refine ⟨e, hxe, ?_⟩
        simpa [heq] using hyf
      exact ⟨.long e (C.label i) f,
        ⟨hne, he, hf, hxe, hyf,
          ⟨e, he, hxe⟩, ⟨f, hf, hyf⟩, hPair⟩⟩
  let pieces : Fin C.length → TrainSupremePiece E P :=
    fun i => Classical.choose (existsGood i)
  have hGood (i : Fin C.length) : Good i (pieces i) :=
    Classical.choose_spec (existsGood i)
  have hNone : ∀ i : Fin C.length, pieces i ≠ .keep := by
    intro i hi
    have hh := hGood i
    rw [hi] at hh
    exact hh
  have hInc : (C.toWagonSeedBigCycle D).LocalPieceIncidence
      (D.wagonSeed) pieces := by
    intro i
    have hh := hGood i
    cases hp : pieces i with
    | keep =>
        exact (hNone i hp).elim
    | short e =>
        rw [hp] at hh
        dsimp [Good] at hh
        change C.vertex (trainCyclicPred i) ∈ D.edgeCarrier e ∧
          C.vertex i ∈ D.edgeCarrier e
        exact hh
    | long e p f =>
        rw [hp] at hh
        dsimp [Good] at hh
        rcases hh with ⟨hne, he, hf, hxe, hyf, _, _, _⟩
        change e ≠ f ∧
          C.vertex (trainCyclicPred i) ∈ D.edgeCarrier e ∧
          D.parent e = p ∧ D.parent f = p ∧
          C.vertex i ∈ D.edgeCarrier f
        exact ⟨hne, hxe, he, hf, hyf⟩
  have hGeom : (C.toWagonSeedBigCycle D).LocalLongA2Geometry
      (D.wagonSeed) pieces := by
    intro i e f p hp
    have hh := hGood i
    rw [hp] at hh
    dsimp [Good] at hh
    rcases hh with ⟨hne, he, hf, hx, hy, hWFirst, hWLast, hNo⟩
    exact ⟨C.vertex (trainCyclicPred i), C.vertex i,
      rfl, rfl, hWFirst, hWLast, hNo⟩
  exact ⟨pieces, hNone, hInc, hGeom⟩

/-- The physically chosen pieces close the last local-geometry premise:
a short labelled cut cycle with a no-chord window contradicts full
system girth, at ANY cutoff at least its length. -/
theorem false_of_chordless_wagon_cycle
    (q : ℕ) (hFull : D.FullSystemGirthGT q)
    (C : LabelledBergeCycle (fun p : P => {x : V | D.WagonVertex p x}))
    (hn : 3 ≤ C.length) (hq : C.length ≤ q)
    (hChordless : ∀ p : P, ∃ i : Fin C.length,
      ∀ j : Fin C.length,
        D.WagonVertex p (C.vertex j) →
        j = i ∨ j = cyclicSucc i) : False := by
  obtain ⟨pieces, hNone, hInc, hGeom⟩ :=
    C.exists_physical_pieces D
  exact D.false_of_chordless_wagon_cycle_and_physical_pieces
    q hFull C hn hq hChordless pieces hNone hInc hGeom

end StructuralRamsey.Girth.OrderOneData

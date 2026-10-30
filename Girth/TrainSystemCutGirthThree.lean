import Girth.TrainSystemCutPhysicalPieces
import Girth.TrainSystemCutTriangleShort
import Mathlib.Tactic

/-!
# The complete wagon-cut girth consequence at cutoff three

Wagon-carrier linearity excludes a labelled two-cycle. It also makes
every three-wagon labelled cycle automatically chordless: a fourth
wagon meeting all three connectors would intersect two of the three
cycle wagons in two vertices. The checked auxiliary-wagon expansion
then produces a physical acceptable edge-only BigCycle of order three,
contradicting the full system-girth bound.

No shortest-cycle selection or appendix argument is needed at this
cutoff. For q > 3, proving shortest labelled cycles are chordless is
the remaining graph-theoretic gap.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Any labelled cut cycle of length three has the exact no-chord
window under complete wagon-carrier linearity. -/
theorem labelledWagonCycle.chordless_of_length_three
    (hLinear : D.LinearPretrain)
    (C : LabelledBergeCycle (fun p : P => {x : V | D.WagonVertex p x}))
    (hLen : C.length = 3) :
    ∀ p : P, ∃ i : Fin C.length,
      ∀ j : Fin C.length, D.WagonVertex p (C.vertex j) →
        j = i ∨ j = cyclicSucc i := by
  let i0 : Fin C.length := ⟨0, by omega⟩
  let i1 : Fin C.length := ⟨1, by omega⟩
  let i2 : Fin C.length := ⟨2, by omega⟩
  have h01 : cyclicSucc i0 = i1 := by
    apply Fin.ext
    simp [cyclicSucc, i0, i1, hLen]
  have h12 : cyclicSucc i1 = i2 := by
    apply Fin.ext
    simp [cyclicSucc, i1, i2, hLen]
  have h20 : cyclicSucc i2 = i0 := by
    apply Fin.ext
    simp [cyclicSucc, i2, i0, hLen]
  have h01ne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have h02ne : i0 ≠ i2 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i2] at this
  have hpne : C.label i0 ≠ C.label i1 := by
    intro h
    exact h01ne (C.label_injective h)
  have hxn : C.vertex i0 ≠ C.vertex i1 := by
    intro h
    exact h01ne (C.vertex_injective h)
  have hzn : C.vertex i0 ≠ C.vertex i2 := by
    intro h
    exact h02ne (C.vertex_injective h)
  have hax : D.WagonVertex (C.label i0) (C.vertex i0) :=
    C.left_mem i0
  have haz : D.WagonVertex (C.label i0) (C.vertex i2) := by
    simpa [h20] using C.right_mem i2
  have hbx : D.WagonVertex (C.label i1) (C.vertex i0) := by
    simpa [h01] using C.right_mem i0
  have hby : D.WagonVertex (C.label i1) (C.vertex i1) :=
    C.left_mem i1
  have hNo : ∀ p : P, ¬ (D.WagonVertex p (C.vertex i0) ∧
        D.WagonVertex p (C.vertex i1) ∧
        D.WagonVertex p (C.vertex i2)) :=
    D.no_three_vertex_wagon_of_two_pairs hLinear
      (C.label i0) (C.label i1) hpne
      (C.vertex i0) (C.vertex i1) (C.vertex i2) hxn hzn
      hax haz hbx hby
  have hAll : ∀ j : Fin C.length, j = i0 ∨ j = i1 ∨ j = i2 := by
    intro j
    have hj := j.isLt
    have jbound : j.val < 3 := by omega
    have : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
    rcases this with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  intro p
  by_cases hx : D.WagonVertex p (C.vertex i0)
  · by_cases hy : D.WagonVertex p (C.vertex i1)
    · have hz : ¬ D.WagonVertex p (C.vertex i2) :=
        fun hz => hNo p ⟨hx, hy, hz⟩
      refine ⟨i0, ?_⟩
      intro j hj
      rcases hAll j with h | h | h
      · exact Or.inl h
      · exact Or.inr (h.trans h01.symm)
      · exact (hz (h ▸ hj)).elim
    · refine ⟨i2, ?_⟩
      intro j hj
      rcases hAll j with h | h | h
      · exact Or.inr (h.trans h20.symm)
      · exact (hy (h ▸ hj)).elim
      · exact Or.inl h
  · refine ⟨i1, ?_⟩
    intro j hj
    rcases hAll j with h | h | h
    · exact (hx (h ▸ hj)).elim
    · exact Or.inl h
    · exact Or.inr (h.trans h12.symm)

/-- Full system girth at cutoff three implies the complete LABELLED
wagon-carrier cut has girth >3. This is stronger than the existing
two-cut lemma and handles all physical short/long piece combinations
through the checked arbitrary-replacement construction. -/
theorem labelledCutGirth_three_of_fullSystemGirth
    (hFull : D.FullSystemGirthGT 3) :
    LabelledGirthGT (fun p : P => {x : V | D.WagonVertex p x}) 3 := by
  rintro ⟨C, hShort⟩
  have hLen : C.length = 2 ∨ C.length = 3 := by
    have := C.hlength
    omega
  rcases hLen with hTwo | hThree
  · have hTwoGirth := D.labelledCutGirth_two_of_fullSystemGirth 3 hFull
    exact hTwoGirth ⟨C, by omega⟩
  · have hChordless :=
      D.labelledWagonCycle.chordless_of_length_three
        hFull.1 C hThree
    exact D.false_of_chordless_wagon_cycle
      3 hFull C (by omega) (by omega) hChordless

end StructuralRamsey.Girth.OrderOneData

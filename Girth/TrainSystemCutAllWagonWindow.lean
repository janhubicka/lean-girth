import Girth.TrainSystemCutFirstWagonWindow
import Girth.TrainSystemCutOutsideWagonWindow
import Girth.TrainSystemCutWindowTransport
import Mathlib.Tactic

/-!
# Global contact windows on a shortest labelled cycle

In a globally shortest labelled Berge cycle of a pairwise-linear
family, EVERY wagon p has all its contacts with the source vertex
connectors within two consecutive cyclic positions:

* if p is one of the cycle labels, rotate that label to first position
  and use the first-wagon shortcut obstruction;
* otherwise rotate any contact to zero and use the outside-wagon
  two-contact obstruction; if p has no contacts the window is empty.

The proof depends only on literal labelled cycle rotation and physical
incidence; it does not use a Ramsey or system-girth hypothesis. This
is the missing geometric chordless-window step in the manuscript.
-/

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- The first wagon in any globally minimal pairwise-linear labelled
cycle meets no connector except its two cyclic boundary vertices. -/
theorem LabelledBergeCycle.first_wagon_contact_window_of_minimal
    (carrier : I → Set V) (C : LabelledBergeCycle carrier)
    (hMin : ∀ B : LabelledBergeCycle carrier, C.length ≤ B.length)
    (hLinear : ∀ a b : I, a ≠ b →
      (carrier a ∩ carrier b).Subsingleton)
    (hn : 3 ≤ C.length) :
    ∃ i : Fin C.length, ∀ j : Fin C.length,
      C.vertex j ∈ carrier (C.label ⟨0, by omega⟩) →
        j = i ∨ j = cyclicSucc i := by
  let z : Fin C.length := ⟨0, by omega⟩
  let last : Fin C.length := ⟨C.length - 1, by omega⟩
  have hSuccLast : cyclicSucc last = z := by
    apply Fin.ext
    change (C.length - 1 + 1) % C.length = 0
    have hsum : C.length - 1 + 1 = C.length := by omega
    rw [hsum, Nat.mod_self]
  refine ⟨last, ?_⟩
  intro j hj
  by_cases hl : j = last
  · exact Or.inl hl
  by_cases hz : j = z
  · exact Or.inr (by rw [hSuccLast]; exact hz)
  have hj1 : 1 ≤ j.val := by
    have hjneq : j.val ≠ 0 := by
      intro hv
      apply hz
      apply Fin.ext
      simpa [z] using hv
    omega
  have hj2 : j.val + 1 < C.length := by
    have hjneq : j.val ≠ C.length - 1 := by
      intro hv
      apply hl
      apply Fin.ext
      simpa [last] using hv
    have := j.isLt
    omega
  have hContact : C.vertex ⟨j.val, by exact j.isLt⟩ ∈
      carrier (C.label ⟨0, by omega⟩) := by simpa using hj
  exact False.elim
    (C.first_wagon_no_extra_of_minimal carrier hMin hLinear
      j.val hj1 hj2 hContact)

/-- An outside wagon of a globally shortest cycle has at most one
connector contact. The A3 adjacent-pair window is therefore automatic.
-/
theorem LabelledBergeCycle.outside_wagon_contact_window_of_minimal
    (carrier : I → Set V) (C : LabelledBergeCycle carrier)
    (hMin : ∀ B : LabelledBergeCycle carrier, C.length ≤ B.length)
    (hLinear : ∀ a b : I, a ≠ b →
      (carrier a ∩ carrier b).Subsingleton)
    (hn : 3 ≤ C.length)
    (p : I) (hOutside : ∀ i : Fin C.length, p ≠ C.label i) :
    ∃ i : Fin C.length, ∀ j : Fin C.length,
      C.vertex j ∈ carrier p →
        j = i ∨ j = cyclicSucc i := by
  by_cases hContact : ∃ s : Fin C.length, C.vertex s ∈ carrier p
  · obtain ⟨s, hs⟩ := hContact
    let R := C.rotate s
    have hnR : 3 ≤ R.length := by simpa [R] using hn
    have hMinR : ∀ B : LabelledBergeCycle carrier, R.length ≤ B.length :=
      C.rotate_minimal hMin s
    have hOutsideR : ∀ j : Fin R.length, p ≠ R.label j := by
      intro j
      change p ≠ C.label ((finCycle s) j)
      exact hOutside ((finCycle s) j)
    let z : Fin R.length := ⟨0, by omega⟩
    have hz : R.vertex z ∈ carrier p := by
      change (C.rotate s).vertex (⟨0, by omega⟩ : Fin C.length) ∈ carrier p
      rw [C.rotate_vertex_zero s]
      exact hs
    have hOnly0 :
        ∀ j : Fin R.length, R.vertex j ∈ carrier p → j = z := by
      intro j hj
      by_contra hne
      have hjpos : 1 ≤ j.val := by
        have hj0 : j.val ≠ 0 := by
          intro heq
          apply hne
          apply Fin.ext
          simpa [z] using heq
        omega
      exact
        (R.outside_wagon_no_second_from_zero carrier hMinR hLinear
          hnR p hOutsideR j.val hjpos j.isLt hz hj).elim
    have hWindowR :
        ∃ i : Fin R.length, ∀ j : Fin R.length,
          R.vertex j ∈ carrier p → j = i ∨ j = cyclicSucc i :=
      ⟨z, fun j hj => Or.inl (hOnly0 j hj)⟩
    exact C.contact_window_of_rotate s p hWindowR
  · let z : Fin C.length := ⟨0, by omega⟩
    refine ⟨z, ?_⟩
    intro j hj
    exact False.elim (hContact ⟨j, hj⟩)

/-- Full labelled chordless contact window: selected wagon labels have
only their two prescribed boundary contacts, while every unselected
wagon has at most one contact. -/
theorem LabelledBergeCycle.contact_window_of_global_minimal
    (carrier : I → Set V) (C : LabelledBergeCycle carrier)
    (hMin : ∀ B : LabelledBergeCycle carrier, C.length ≤ B.length)
    (hLinear : ∀ a b : I, a ≠ b →
      (carrier a ∩ carrier b).Subsingleton)
    (hn : 3 ≤ C.length) :
    ∀ p : I, ∃ i : Fin C.length, ∀ j : Fin C.length,
      C.vertex j ∈ carrier p →
        j = i ∨ j = cyclicSucc i := by
  intro p
  by_cases hOn : ∃ s : Fin C.length, C.label s = p
  · obtain ⟨s, hs⟩ := hOn
    let R := C.rotate s
    have hnR : 3 ≤ R.length := by simpa [R] using hn
    have hMinR : ∀ B : LabelledBergeCycle carrier, R.length ≤ B.length :=
      C.rotate_minimal hMin s
    have hFirst : R.label (⟨0, by omega⟩ : Fin R.length) = p := by
      change (C.rotate s).label
        (⟨0, by omega⟩ : Fin C.length) = p
      rw [C.rotate_label_zero s]
      exact hs
    have hWindowR :
        ∃ i : Fin R.length, ∀ j : Fin R.length,
          R.vertex j ∈ carrier p → j = i ∨ j = cyclicSucc i := by
      have h0 := R.first_wagon_contact_window_of_minimal
        carrier hMinR hLinear hnR
      simpa only [hFirst] using h0
    exact C.contact_window_of_rotate s p hWindowR
  · have hOutside : ∀ i : Fin C.length, p ≠ C.label i := by
      intro i heq
      exact hOn ⟨i, heq.symm⟩
    exact C.outside_wagon_contact_window_of_minimal
      carrier hMin hLinear hn p hOutside

end StructuralRamsey.Girth

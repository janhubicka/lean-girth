import Girth.TrainSystemCutMinimalCycle
import Mathlib.Tactic

/-!
# A literal prefix shortcut in a labelled Berge cycle

Let C be a labelled Berge cycle with n positions. If an additional
wagon p contains connector 0 and connector k, with 2 <= k and
k+1 < n, and p differs from every existing label at positions 1..k,
then the labels at positions 1..k followed by p make a strictly
shorter labelled Berge cycle. No identification of equal physical
carriers or new physical edges is permitted.

This is the common combinatorial shortcut needed for the omitted
selected-wagon and outside-wagon contact cases. Rotating an arbitrary
cycle and choosing which arc to keep are separate tasks.
-/

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- Splice a genuine wagon label across connectors 0 and k.
The new cycle keeps the original labels 1,...,k and closes by p.
All connector and label injectivity properties are proved literally. -/
theorem LabelledBergeCycle.exists_prefix_shortcut
    (carrier : I → Set V) (C : LabelledBergeCycle carrier)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k + 1 < C.length)
    (p : I)
    (hp0 : C.vertex ⟨0, by omega⟩ ∈ carrier p)
    (hpk : C.vertex ⟨k, by omega⟩ ∈ carrier p)
    (hFresh : ∀ t : ℕ, 1 ≤ t → t ≤ k →
      p ≠ C.label ⟨t, by omega⟩) :
    ∃ B : LabelledBergeCycle carrier,
      B.length = k + 1 ∧ B.length < C.length := by
  classical
  let lab : Fin (k + 1) → I := fun i =>
    if h : i.val < k then C.label ⟨i.val + 1, by omega⟩ else p
  let vert : Fin (k + 1) → V := fun i =>
    if h : i.val < k then C.vertex ⟨i.val + 1, by omega⟩
    else C.vertex ⟨0, by omega⟩
  have hLab (i : Fin (k + 1)) (hi : i.val < k) :
      lab i = C.label ⟨i.val + 1, by omega⟩ := by
    simp only [lab, dif_pos hi]
  have hLabLast (i : Fin (k + 1)) (hi : ¬ i.val < k) :
      lab i = p := by simp only [lab, dif_neg hi]
  have hVert (i : Fin (k + 1)) (hi : i.val < k) :
      vert i = C.vertex ⟨i.val + 1, by omega⟩ := by
    simp only [vert, dif_pos hi]
  have hVertLast (i : Fin (k + 1)) (hi : ¬ i.val < k) :
      vert i = C.vertex ⟨0, by omega⟩ := by
    simp only [vert, dif_neg hi]
  have hLabInj : Function.Injective lab := by
    intro i j hij
    by_cases hi : i.val < k
    · by_cases hj : j.val < k
      · have hc :
          C.label ⟨i.val + 1, by omega⟩ =
            C.label ⟨j.val + 1, by omega⟩ := by
          simpa only [hLab i hi, hLab j hj] using hij
        have heq := C.label_injective hc
        apply Fin.ext
        have hv := congrArg Fin.val heq
        omega
      · have hc : C.label ⟨i.val + 1, by omega⟩ = p := by
          simpa only [hLab i hi, hLabLast j hj] using hij
        exact (hFresh (i.val + 1) (by omega) (by omega) hc.symm).elim
    · by_cases hj : j.val < k
      · have hc : p = C.label ⟨j.val + 1, by omega⟩ := by
          simpa only [hLabLast i hi, hLab j hj] using hij
        exact (hFresh (j.val + 1) (by omega) (by omega) hc).elim
      · apply Fin.ext
        have hival := i.isLt
        have hjval := j.isLt
        omega
  have hVertInj : Function.Injective vert := by
    intro i j hij
    by_cases hi : i.val < k
    · by_cases hj : j.val < k
      · have hc :
          C.vertex ⟨i.val + 1, by omega⟩ =
            C.vertex ⟨j.val + 1, by omega⟩ := by
          simpa only [hVert i hi, hVert j hj] using hij
        have heq := C.vertex_injective hc
        apply Fin.ext
        have hv := congrArg Fin.val heq
        omega
      · have hc : C.vertex ⟨i.val + 1, by omega⟩ =
            C.vertex ⟨0, by omega⟩ := by
          simpa only [hVert i hi, hVertLast j hj] using hij
        have heq := C.vertex_injective hc
        have hv := congrArg Fin.val heq
        omega
    · by_cases hj : j.val < k
      · have hc : C.vertex ⟨0, by omega⟩ =
            C.vertex ⟨j.val + 1, by omega⟩ := by
          simpa only [hVertLast i hi, hVert j hj] using hij
        have heq := C.vertex_injective hc
        have hv := congrArg Fin.val heq
        omega
      · apply Fin.ext
        have hival := i.isLt
        have hjval := j.isLt
        omega
  have hSucc (i : Fin (k + 1)) (hi : i.val < k) :
      (cyclicSucc i).val = i.val + 1 := by
    change (i.val + 1) % (k + 1) = i.val + 1
    rw [Nat.mod_eq_of_lt (by omega)]
  let B : LabelledBergeCycle carrier := {
    length := k + 1
    hlength := by omega
    label := lab
    vertex := vert
    label_injective := hLabInj
    vertex_injective := hVertInj
    left_mem := by
      intro i
      by_cases hi : i.val < k
      · simpa [hLab i hi, hVert i hi] using
          (C.left_mem (⟨i.val + 1, by omega⟩ : Fin C.length))
      · have hLast : i.val = k := by have := i.isLt; omega
        simpa [hLabLast i hi, hVertLast i hi] using hp0
    right_mem := by
      intro i
      by_cases hi : i.val < k
      · have hnext := hSucc i hi
        by_cases hmiddle : i.val + 1 < k
        · have hSuccOrig :
            cyclicSucc (⟨i.val + 1, by omega⟩ : Fin C.length) =
              ⟨i.val + 2, by omega⟩ := by
            apply Fin.ext
            change (i.val + 2) % C.length = i.val + 2
            rw [Nat.mod_eq_of_lt (by omega)]
          have hc := C.right_mem (⟨i.val + 1, by omega⟩ : Fin C.length)
          rw [hSuccOrig] at hc
          have hnextCut : (cyclicSucc i).val < k := by omega
          simpa [hVert i hi, hLab (cyclicSucc i) hnextCut,
            hnext] using hc
        · have hkEq : i.val + 1 = k := by omega
          have hnextCut : ¬ (cyclicSucc i).val < k := by omega
          simpa [hVert i hi, hLabLast (cyclicSucc i) hnextCut,
            hkEq] using hpk
      · have hik : i.val = k := by have := i.isLt; omega
        have hsucc : cyclicSucc i =
            (⟨0, by omega⟩ : Fin (k + 1)) := by
          apply Fin.ext
          change (i.val + 1) % (k + 1) = 0
          rw [hik, Nat.mod_self]
        have hOrig :
            cyclicSucc (⟨0, by omega⟩ : Fin C.length) =
              (⟨1, by omega⟩ : Fin C.length) := by
          apply Fin.ext
          change (0 + 1) % C.length = 1
          rw [Nat.mod_eq_of_lt (by omega)]
        have hc := C.right_mem (⟨0, by omega⟩ : Fin C.length)
        rw [hOrig] at hc
        have hzero : ((⟨0, by omega⟩ : Fin (k + 1)).val < k) := by
          change 0 < k
          omega
        simpa [hVertLast i hi, hsucc, hLab _ hzero] using hc
  exact ⟨B, rfl, hkn⟩

end StructuralRamsey.Girth

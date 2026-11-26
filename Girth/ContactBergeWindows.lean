import Girth.ContactBadCycle
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Nat.Find

/-! Globally shortest labelled Berge cycles.
The following pure finite-cycle arguments are extracted from the old
TrainSystemCut* library at 99d26270. Names are isolated from the legacy
modules so that the integration can still import both. No old
supreme-cycle premise occurs. -/

namespace StructuralRamsey.Girth

private theorem contactCyclicSucc_eq_finRotate {n : ℕ} (i : Fin n) :
    cyclicSucc i = finRotate n i := by
  letI := i.neZero
  apply Fin.ext
  simp [cyclicSucc, finRotate_apply, Fin.add_def]

private theorem contactFinCycle_commutes {n : ℕ} (s i : Fin n) :
    (finCycle s) (cyclicSucc i) = cyclicSucc ((finCycle s) i) := by
  rw [contactCyclicSucc_eq_finRotate, contactCyclicSucc_eq_finRotate]
  simp only [finRotate_apply, finCycle_apply]
  ac_rfl

end StructuralRamsey.Girth


namespace StructuralRamsey.Girth

universe v
variable {V P E I : Type v}

/-- Pairwise linearity of a *labelled* family excludes its genuine
labelled Berge two-cycles. Distinct labels are not identified by
equality of their carriers. -/
theorem contactLabelledGirthGT_two_of_pairwiseSubsingleton
    (carrier : P → Set V)
    (hPair : ∀ p q : P, p ≠ q →
      (carrier p ∩ carrier q).Subsingleton) :
    LabelledGirthGT carrier 2 := by
  rintro ⟨C, hSmall⟩
  obtain ⟨n, hn, label, vertex, hLabel, hVertex, hLeft, hRight⟩ := C
  have hLength : n = 2 := by
    change n ≤ 2 at hSmall
    omega
  subst n
  have hpq : label 0 ≠ label 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (hLabel h)
  have hx : vertex 0 ∈ carrier (label 0) ∩ carrier (label 1) := by
    exact ⟨hLeft 0, by simpa [cyclicSucc] using hRight 0⟩
  have hy : vertex 1 ∈ carrier (label 0) ∩ carrier (label 1) := by
    exact ⟨by simpa [cyclicSucc] using hRight 1, hLeft 1⟩
  have hEq : vertex 0 = vertex 1 := hPair _ _ hpq hx hy
  exact (by decide : (0 : Fin 2) ≠ 1) (hVertex hEq)

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- A failed labelled cut-girth bound supplies an actual globally
minimum-length labelled Berge cycle, with length within the failed
budget. The minimization is over ALL labels and ALL physical cycles,
not only over the chosen cycle's support. -/
theorem LabelledGirthGT.contact_exists_global_minimal_cycle_of_failure
    (carrier : I → Set V) (q : ℕ)
    (hFail : ¬ LabelledGirthGT carrier q) :
    ∃ C : LabelledBergeCycle carrier,
      C.length ≤ q ∧
      ∀ B : LabelledBergeCycle carrier, C.length ≤ B.length := by
  classical
  have hExists : ∃ C : LabelledBergeCycle carrier, C.length ≤ q := by
    exact Classical.not_not.mp hFail
  let P : ℕ → Prop :=
    fun n => ∃ C : LabelledBergeCycle carrier, C.length = n
  have hNonempty : ∃ n : ℕ, P n := by
    obtain ⟨C, _hBound⟩ := hExists
    exact ⟨C.length, C, rfl⟩
  obtain ⟨C, hC⟩ : P (Nat.find hNonempty) :=
    Nat.find_spec hNonempty
  refine ⟨C, ?_, ?_⟩
  · obtain ⟨C0, hC0⟩ := hExists
    have hMin : Nat.find hNonempty ≤ C0.length :=
      Nat.find_min' hNonempty (show P C0.length from ⟨C0, rfl⟩)
    omega
  · intro B
    have hMin : Nat.find hNonempty ≤ B.length :=
      Nat.find_min' hNonempty (show P B.length from ⟨B, rfl⟩)
    omega

/-- An independently selected globally minimal cut cycle cannot
have a strictly shorter labelled cycle. This is the direct interface
for the future chord-shortening contradiction. -/
theorem LabelledBergeCycle.contact_no_shorter_of_global_minimal
    (carrier : I → Set V)
    (C : LabelledBergeCycle carrier)
    (hMinimal :
      ∀ B : LabelledBergeCycle carrier, C.length ≤ B.length) :
    ¬ ∃ B : LabelledBergeCycle carrier, B.length < C.length := by
  rintro ⟨B, hShort⟩
  exact (Nat.not_lt_of_ge (hMinimal B)) hShort

/-- In a pairwise-linear family, the globally shortest labelled
cycle has length at least three: a labelled length-two cycle would
give two different wagon labels sharing two distinct vertices. -/
theorem LabelledGirthGT.contact_exists_minimal_three_of_failure
    (carrier : I → Set V) (q : ℕ)
    (hLinear : ∀ a b : I, a ≠ b →
      (carrier a ∩ carrier b).Subsingleton)
    (hFail : ¬ LabelledGirthGT carrier q) :
    ∃ C : LabelledBergeCycle carrier,
      3 ≤ C.length ∧ C.length ≤ q ∧
      ∀ B : LabelledBergeCycle carrier, C.length ≤ B.length := by
  obtain ⟨C, hBudget, hMin⟩ :=
    LabelledGirthGT.contact_exists_global_minimal_cycle_of_failure carrier q hFail
  have hTwo : LabelledGirthGT carrier 2 :=
    contactLabelledGirthGT_two_of_pairwiseSubsingleton carrier hLinear
  have hNotTwo : ¬ C.length ≤ 2 :=
    fun hLength => hTwo ⟨C, hLength⟩
  exact ⟨C, by omega, hBudget, hMin⟩

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- Splice a genuine wagon label across connectors 0 and k.
The new cycle keeps the original labels 1,...,k and closes by p.
All connector and label injectivity properties are proved literally. -/
theorem LabelledBergeCycle.contact_exists_prefix_shortcut
    (carrier : I → Set V) (C : LabelledBergeCycle carrier)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k + 1 < C.length)
    (p : I)
    (hp0 : C.vertex ⟨0, by omega⟩ ∈ carrier p)
    (hpk : C.vertex ⟨k, by omega⟩ ∈ carrier p)
    (hFresh : ∀ t : Fin C.length, 1 ≤ t.val → t.val ≤ k →
      p ≠ C.label t) :
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
        have hv : i.val + 1 = j.val + 1 := by
          simpa using congrArg Fin.val heq
        omega
      · have hc : C.label ⟨i.val + 1, by omega⟩ = p := by
          simpa only [hLab i hi, hLabLast j hj] using hij
        let t : Fin C.length := ⟨i.val + 1, by omega⟩
        have ht : 1 ≤ t.val := by dsimp [t]; omega
        have htk : t.val ≤ k := by dsimp [t]; omega
        exact (hFresh t ht htk hc.symm).elim
    · by_cases hj : j.val < k
      · have hc : p = C.label ⟨j.val + 1, by omega⟩ := by
          simpa only [hLabLast i hi, hLab j hj] using hij
        let t : Fin C.length := ⟨j.val + 1, by omega⟩
        have ht : 1 ≤ t.val := by dsimp [t]; omega
        have htk : t.val ≤ k := by dsimp [t]; omega
        exact (hFresh t ht htk hc).elim
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
        have hv : i.val + 1 = j.val + 1 := by
          simpa using congrArg Fin.val heq
        omega
      · have hc : C.vertex ⟨i.val + 1, by omega⟩ =
            C.vertex ⟨0, by omega⟩ := by
          simpa only [hVert i hi, hVertLast j hj] using hij
        have heq := C.vertex_injective hc
        have hv : i.val + 1 = 0 := by
          simpa using congrArg Fin.val heq
        omega
    · by_cases hj : j.val < k
      · have hc : C.vertex ⟨0, by omega⟩ =
            C.vertex ⟨j.val + 1, by omega⟩ := by
          simpa only [hVertLast i hi, hVert j hj] using hij
        have heq := C.vertex_injective hc
        have hv : 0 = j.val + 1 := by
          simpa using congrArg Fin.val heq
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
        have hzlabel : lab (⟨0, by omega⟩ : Fin (k + 1)) =
            C.label (⟨1, by omega⟩ : Fin C.length) :=
          hLab (⟨0, by omega⟩ : Fin (k + 1)) hzero
        change vert i ∈ carrier (lab (cyclicSucc i))
        rw [hVertLast i hi, hsucc, hzlabel]
        exact hc
    }
  exact ⟨B, rfl, hkn⟩

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- No additional vertex connector of a globally shortest labelled
cycle lies in its first wagon, except the two prescribed boundary
vertices. In particular the forbidden index k may be adjacent to
zero: that case is discharged by physical wagon linearity. -/
theorem LabelledBergeCycle.contact_first_wagon_no_extra_of_minimal
    (carrier : I → Set V) (C : LabelledBergeCycle carrier)
    (hMin : ∀ B : LabelledBergeCycle carrier, C.length ≤ B.length)
    (hLinear : ∀ a b : I, a ≠ b →
      (carrier a ∩ carrier b).Subsingleton)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 < C.length)
    (hContact :
      C.vertex ⟨k, by omega⟩ ∈
        carrier (C.label ⟨0, by omega⟩)) : False := by
  let z : Fin C.length := ⟨0, by omega⟩
  by_cases hk1 : k = 1
  · subst k
    let o : Fin C.length := ⟨1, by omega⟩
    have hzo : z ≠ o := by
      intro h
      have hv := congrArg Fin.val h
      simp [z, o] at hv
    have hLab : C.label z ≠ C.label o :=
      fun h => hzo (C.label_injective h)
    have hSucc : cyclicSucc z = o := by
      apply Fin.ext
      change (0 + 1) % C.length = 1
      rw [Nat.mod_eq_of_lt (by omega)]
    have hV0a : C.vertex z ∈ carrier (C.label z) :=
      C.left_mem z
    have hV0b : C.vertex z ∈ carrier (C.label o) := by
      simpa only [hSucc] using C.right_mem z
    have hV1a : C.vertex o ∈ carrier (C.label z) := by
      simpa only [o, z] using hContact
    have hV1b : C.vertex o ∈ carrier (C.label o) :=
      C.left_mem o
    have hEq : C.vertex z = C.vertex o :=
      hLinear (C.label z) (C.label o) hLab
        ⟨hV0a, hV0b⟩ ⟨hV1a, hV1b⟩
    exact hzo (C.vertex_injective hEq)
  · have hk2 : 2 ≤ k := by omega
    have hFresh : ∀ t : Fin C.length, 1 ≤ t.val → t.val ≤ k →
        C.label z ≠ C.label t := by
      intro t ht htk heq
      have heqFin := C.label_injective heq
      have hv := congrArg Fin.val heqFin
      change 0 = t.val at hv
      omega
    obtain ⟨B, _hLen, hShort⟩ :=
      C.contact_exists_prefix_shortcut carrier k hk2 hkn (C.label z)
        (C.left_mem z) hContact hFresh
    exact (Nat.not_lt_of_ge (hMin B)) hShort

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- For a globally minimal labelled cycle, an outside wagon meeting
connector zero cannot meet any later connector, including the cyclic
last connector. The endpoint cases use only carrier linearity. -/
theorem LabelledBergeCycle.contact_outside_wagon_no_second_from_zero
    (carrier : I → Set V) (C : LabelledBergeCycle carrier)
    (hMin : ∀ B : LabelledBergeCycle carrier, C.length ≤ B.length)
    (hLinear : ∀ a b : I, a ≠ b →
      (carrier a ∩ carrier b).Subsingleton)
    (hn : 3 ≤ C.length)
    (p : I) (hOutside : ∀ i : Fin C.length, p ≠ C.label i)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k < C.length)
    (hp0 : C.vertex ⟨0, by omega⟩ ∈ carrier p)
    (hpk : C.vertex ⟨k, by omega⟩ ∈ carrier p) : False := by
  let z : Fin C.length := ⟨0, by omega⟩
  let u : Fin C.length := ⟨k, hkn⟩
  have hzu : z ≠ u := by
    intro h
    have hv := congrArg Fin.val h
    have hz : z.val = 0 := rfl
    have hu : u.val = k := rfl
    omega
  have hvzu : C.vertex z ≠ C.vertex u :=
    fun h => hzu (C.vertex_injective h)
  by_cases hk1 : k = 1
  · subst k
    let o : Fin C.length := ⟨1, by omega⟩
    have hSucc : cyclicSucc z = o := by
      apply Fin.ext
      change (0 + 1) % C.length = 1
      rw [Nat.mod_eq_of_lt (by omega)]
    have hV0o : C.vertex z ∈ carrier (C.label o) := by
      simpa only [hSucc] using C.right_mem z
    have hV1o : C.vertex o ∈ carrier (C.label o) :=
      C.left_mem o
    have hV1p : C.vertex o ∈ carrier p := by
      simpa only [o, u] using hpk
    have hEq : C.vertex z = C.vertex o :=
      hLinear p (C.label o) (hOutside o)
        ⟨hp0, hV0o⟩ ⟨hV1p, hV1o⟩
    have heq : z = o := C.vertex_injective hEq
    have hv := congrArg Fin.val heq
    simp [z, o] at hv
  · by_cases hkLast : k + 1 = C.length
    · let last : Fin C.length := ⟨C.length - 1, by omega⟩
      have hlast : k = C.length - 1 := by omega
      have hSucc : cyclicSucc last = z := by
        apply Fin.ext
        change (C.length - 1 + 1) % C.length = 0
        have hsum : C.length - 1 + 1 = C.length := by omega
        rw [hsum, Nat.mod_self]
      have hVlast0 : C.vertex last ∈ carrier (C.label z) := by
        simpa only [hSucc] using C.right_mem last
      have hVlastp : C.vertex last ∈ carrier p := by
        simpa [last, hlast] using hpk
      have hEq : C.vertex z = C.vertex last :=
        hLinear p (C.label z) (hOutside z)
          ⟨hp0, C.left_mem z⟩ ⟨hVlastp, hVlast0⟩
      have hZe : z = last := C.vertex_injective hEq
      have hv := congrArg Fin.val hZe
      simp [z, last] at hv
      omega
    · have hk2 : 2 ≤ k := by omega
      have hkBefore : k + 1 < C.length := by omega
      have hFresh : ∀ t : Fin C.length, 1 ≤ t.val → t.val ≤ k →
          p ≠ C.label t := by
        intro t ht htk
        exact hOutside t
      obtain ⟨B, _hLen, hShort⟩ :=
        C.contact_exists_prefix_shortcut carrier k hk2 hkBefore p
          hp0 hpk hFresh
      exact (Nat.not_lt_of_ge (hMin B)) hShort

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- Rotate a labelled Berge cycle by a genuine cyclic equivalence. -/
def LabelledBergeCycle.contactRotate
    {carrier : I → Set V} (C : LabelledBergeCycle carrier)
    (s : Fin C.length) : LabelledBergeCycle carrier where
  length := C.length
  hlength := C.hlength
  label i := C.label ((finCycle s) i)
  vertex i := C.vertex ((finCycle s) i)
  label_injective := by
    intro i j h
    exact (finCycle s).injective (C.label_injective h)
  vertex_injective := by
    intro i j h
    exact (finCycle s).injective (C.vertex_injective h)
  left_mem := fun i => C.left_mem ((finCycle s) i)
  right_mem := by
    intro i
    change C.vertex ((finCycle s) i) ∈
      carrier (C.label ((finCycle s) (cyclicSucc i)))
    rw [contactFinCycle_commutes]
    exact C.right_mem ((finCycle s) i)

/-- Rotation preserves the exact count of distinct labelled wagons. -/
@[simp] theorem LabelledBergeCycle.contactRotate_length
    {carrier : I → Set V} (C : LabelledBergeCycle carrier)
    (s : Fin C.length) : (C.contactRotate s).length = C.length := rfl

/-- Rotation sends the chosen source connector to index zero. -/
theorem LabelledBergeCycle.contactRotate_vertex_zero
    {carrier : I → Set V} (C : LabelledBergeCycle carrier)
    (s : Fin C.length) :
    (C.contactRotate s).vertex
        (⟨0, by have h := C.hlength; omega⟩ : Fin C.length) =
      C.vertex s := by
  change C.vertex ((finCycle s) (⟨0, by have h := C.hlength; omega⟩ : Fin C.length)) =
    C.vertex s
  congr 1
  rw [finCycle_apply]
  apply Fin.ext
  rw [Fin.val_add]
  simpa using (Nat.mod_eq_of_lt s.isLt)

/-- The same rotation sends the chosen original wagon label to zero. -/
theorem LabelledBergeCycle.contactRotate_label_zero
    {carrier : I → Set V} (C : LabelledBergeCycle carrier)
    (s : Fin C.length) :
    (C.contactRotate s).label
        (⟨0, by have h := C.hlength; omega⟩ : Fin C.length) =
      C.label s := by
  change C.label ((finCycle s) (⟨0, by have h := C.hlength; omega⟩ : Fin C.length)) =
    C.label s
  congr 1
  rw [finCycle_apply]
  apply Fin.ext
  rw [Fin.val_add]
  simpa using (Nat.mod_eq_of_lt s.isLt)

/-- A globally minimal labelled cycle remains globally minimal
under rotation, since its length is literally unchanged. -/
theorem LabelledBergeCycle.contactRotate_minimal
    {carrier : I → Set V} (C : LabelledBergeCycle carrier)
    (hMin : ∀ B : LabelledBergeCycle carrier, C.length ≤ B.length)
    (s : Fin C.length) :
    ∀ B : LabelledBergeCycle carrier, (C.contactRotate s).length ≤ B.length :=
  hMin

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- Recover the original labelled cycle's A3 window from one rotated
window, including exact successor identities at the cyclic wrap. -/
theorem LabelledBergeCycle.contact_window_of_contactRotate
    {carrier : I → Set V} (C : LabelledBergeCycle carrier)
    (s : Fin C.length) (p : I)
    (h :
      ∃ i : Fin (C.contactRotate s).length,
        ∀ j : Fin (C.contactRotate s).length,
          (C.contactRotate s).vertex j ∈ carrier p →
            j = i ∨ j = cyclicSucc i) :
    ∃ i : Fin C.length, ∀ j : Fin C.length,
        C.vertex j ∈ carrier p → j = i ∨ j = cyclicSucc i := by
  obtain ⟨i, hi⟩ := h
  let iC : Fin C.length := (finCycle s) i
  refine ⟨iC, ?_⟩
  intro j hj
  let jR : Fin C.length := (finCycle s).symm j
  have hMap : (finCycle s) jR = j :=
    Equiv.apply_symm_apply (finCycle s) j
  have hjR : (C.contactRotate s).vertex jR ∈ carrier p := by
    change C.vertex ((finCycle s) jR) ∈ carrier p
    rw [hMap]
    exact hj
  rcases hi jR hjR with heq | heq
  · left
    change j = (finCycle s) i
    calc
      j = (finCycle s) jR := hMap.symm
      _ = (finCycle s) i := congrArg (finCycle s) heq
  · right
    change j = cyclicSucc ((finCycle s) i)
    calc
      j = (finCycle s) jR := hMap.symm
      _ = (finCycle s) (cyclicSucc i) :=
        congrArg (finCycle s) heq
      _ = cyclicSucc ((finCycle s) i) :=
        contactFinCycle_commutes s i

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- The first wagon in any globally minimal pairwise-linear labelled
cycle meets no connector except its two cyclic boundary vertices. -/
theorem LabelledBergeCycle.contact_first_wagon_contact_window_of_minimal
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
    (C.contact_first_wagon_no_extra_of_minimal carrier hMin hLinear
      j.val hj1 hj2 hContact)

/-- An outside wagon of a globally shortest cycle has at most one
connector contact. The A3 adjacent-pair window is therefore automatic.
-/
theorem LabelledBergeCycle.contact_outside_wagon_contact_window_of_minimal
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
    let R := C.contactRotate s
    have hnR : 3 ≤ R.length := by simpa [R] using hn
    have hMinR : ∀ B : LabelledBergeCycle carrier, R.length ≤ B.length :=
      C.contactRotate_minimal hMin s
    have hOutsideR : ∀ j : Fin R.length, p ≠ R.label j := by
      intro j
      change p ≠ C.label ((finCycle s) j)
      exact hOutside ((finCycle s) j)
    let z : Fin R.length := ⟨0, by omega⟩
    have hz : R.vertex z ∈ carrier p := by
      change (C.contactRotate s).vertex (⟨0, by omega⟩ : Fin C.length) ∈ carrier p
      rw [C.contactRotate_vertex_zero s]
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
        (R.contact_outside_wagon_no_second_from_zero carrier hMinR hLinear
          hnR p hOutsideR j.val hjpos j.isLt hz hj).elim
    have hWindowR :
        ∃ i : Fin R.length, ∀ j : Fin R.length,
          R.vertex j ∈ carrier p → j = i ∨ j = cyclicSucc i :=
      ⟨z, fun j hj => Or.inl (hOnly0 j hj)⟩
    exact C.contact_window_of_contactRotate s p hWindowR
  · let z : Fin C.length := ⟨0, by omega⟩
    refine ⟨z, ?_⟩
    intro j hj
    exact False.elim (hContact ⟨j, hj⟩)

/-- Full labelled chordless contact window: selected wagon labels have
only their two prescribed boundary contacts, while every unselected
wagon has at most one contact. -/
theorem LabelledBergeCycle.contact_shortest_window
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
    let R := C.contactRotate s
    have hnR : 3 ≤ R.length := by simpa [R] using hn
    have hMinR : ∀ B : LabelledBergeCycle carrier, R.length ≤ B.length :=
      C.contactRotate_minimal hMin s
    have hFirst : R.label (⟨0, by omega⟩ : Fin R.length) = p := by
      change (C.contactRotate s).label
        (⟨0, by omega⟩ : Fin C.length) = p
      rw [C.contactRotate_label_zero s]
      exact hs
    have hWindowR :
        ∃ i : Fin R.length, ∀ j : Fin R.length,
          R.vertex j ∈ carrier p → j = i ∨ j = cyclicSucc i := by
      have h0 := R.contact_first_wagon_contact_window_of_minimal
        carrier hMinR hLinear hnR
      simpa only [hFirst] using h0
    exact C.contact_window_of_contactRotate s p hWindowR
  · have hOutside : ∀ i : Fin C.length, p ≠ C.label i := by
      intro i heq
      exact hOn ⟨i, heq.symm⟩
    exact C.contact_outside_wagon_contact_window_of_minimal
      carrier hMin hLinear hn p hOutside

end StructuralRamsey.Girth

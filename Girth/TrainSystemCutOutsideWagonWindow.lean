import Girth.TrainSystemCutPrefixShortcut
import Mathlib.Tactic

/-!
# An outside wagon cannot meet two connectors of a shortest cycle

Take a globally shortest labelled Berge cycle in a pairwise-linear
wagon family. A wagon label that is NOT among its labels cannot contain
two distinct cycle connector vertices. If those connectors are
consecutive, their original intervening wagon shares the same pair,
contradicting linearity. If they are nonconsecutive, the literal prefix
shortcut makes a strictly shorter labelled cycle. All cases retain
genuine labelled wagon identities.
-/

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- For a globally minimal labelled cycle, an outside wagon meeting
connector zero cannot meet any later connector, including the cyclic
last connector. The endpoint cases use only carrier linearity. -/
theorem LabelledBergeCycle.outside_wagon_no_second_from_zero
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
      have hFresh : ∀ t : ℕ, 1 ≤ t → t ≤ k →
          p ≠ C.label ⟨t, by omega⟩ := by
        intro t ht htk
        exact hOutside ⟨t, by omega⟩
      obtain ⟨B, _hLen, hShort⟩ :=
        C.exists_prefix_shortcut carrier k hk2 hkBefore p
          hp0 hpk hFresh
      exact (Nat.not_lt_of_ge (hMin B)) hShort

end StructuralRamsey.Girth

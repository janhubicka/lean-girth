import Girth.TrainSystemCutPrefixShortcut
import Mathlib.Tactic

/-!
# A shortest labelled cycle has no extra contact with its first wagon

The chosen first wagon contains the cycle connectors at its own two
ends: positions zero and n-1. Every further contact at position
1..n-2 is impossible. At position 1, two distinct wagon labels
would contain two distinct connectors, violating pairwise linearity.
At position >=2, the prefix-shortcut constructor produces a strictly
shorter labelled cycle, contradicting global minimality.

The full contact-window theorem for all selected and outside wagons
still needs cyclic rotations and choice of an admissible shortcut arc.
No appendix material is used.
-/

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- No additional vertex connector of a globally shortest labelled
cycle lies in its first wagon, except the two prescribed boundary
vertices. In particular the forbidden index k may be adjacent to
zero: that case is discharged by physical wagon linearity. -/
theorem LabelledBergeCycle.first_wagon_no_extra_of_minimal
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
      C.exists_prefix_shortcut carrier k hk2 hkn (C.label z)
        (C.left_mem z) hContact hFresh
    exact (Nat.not_lt_of_ge (hMin B)) hShort

end StructuralRamsey.Girth

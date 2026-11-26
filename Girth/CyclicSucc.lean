import Mathlib.Tactic

namespace StructuralRamsey.Girth

/-- Cyclic successor on a nonempty finite index type. -/
def cyclicSucc {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.2)⟩

end StructuralRamsey.Girth

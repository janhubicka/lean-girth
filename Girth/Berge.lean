import Girth.Support

/-! # Berge cycles and support girth

Instead of adjoining an infinity value, the formalization uses the proposition
`GirthGT H g`: the hypergraph `H` has no Berge cycle of length at most
`g`.  This is exactly the form used by the main theorem.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- Cyclic successor on a nonempty finite index type. -/
def cyclicSucc {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.2)⟩

/-- A Berge cycle with distinct edges and distinct connecting vertices. -/
structure BergeCycle (H : Set (Set W)) where
  length : ℕ
  hlength : 2 ≤ length
  edge : Fin length → Set W
  vertex : Fin length → W
  edge_mem : ∀ i, edge i ∈ H
  edge_injective : Function.Injective edge
  vertex_injective : Function.Injective vertex
  left_mem : ∀ i, vertex i ∈ edge i
  right_mem : ∀ i, vertex i ∈ edge (cyclicSucc i)

/-- The hypergraph has a Berge cycle of length at most `g`. -/
def HasBergeCycleAtMost (H : Set (Set W)) (g : ℕ) : Prop :=
  ∃ c : BergeCycle H, c.length ≤ g

/-- Girth strictly greater than `g`, expressed without an infinity value. -/
def GirthGT (H : Set (Set W)) (g : ℕ) : Prop :=
  ¬ HasBergeCycleAtMost H g

theorem girthGT_mono {H : Set (Set W)} {g h : ℕ}
    (hgt : GirthGT H g) (hhg : h ≤ g) :
    GirthGT H h := by
  intro hc
  rcases hc with ⟨c, hc⟩
  exact hgt ⟨c, hc.trans hhg⟩

theorem girthGT_one (H : Set (Set W)) : GirthGT H 1 := by
  rintro ⟨c, hc⟩
  omega

end StructuralRamsey.Girth

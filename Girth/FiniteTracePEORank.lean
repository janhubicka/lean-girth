import Girth.FiniteTraceSimplicialCriterion
import Mathlib.Order.Basic

/-!
# Turn a finite elimination ranking into an actual LinearOrder

Deleting a simplicial vertex at each step constructs an injective ranking
whose strictly later neighbours form a clique. Mathlib's LinearOrder.lift'
turns that ranking into a perfect elimination order.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

/-- A numerical certificate for a perfect elimination ordering. -/
def IsPerfectEliminationRanking
    (G : SimpleGraph V) (rank : V → ℕ) : Prop :=
  Function.Injective rank ∧
    ∀ v x y : V,
      rank v < rank x → rank v < rank y → x ≠ y →
        G.Adj v x → G.Adj v y → G.Adj x y

/-- A valid injective ranking canonically induces a linear order
for which the graph has the PEO property. No cycle theorem is
being postulated by this adapter. -/
theorem exists_perfectEliminationOrder_of_ranking
    (G : SimpleGraph V) (rank : V → ℕ)
    (hRank : IsPerfectEliminationRanking G rank) :
    ∃ order : LinearOrder V,
      @IsPerfectEliminationOrder V order G := by
  let order : LinearOrder V :=
    LinearOrder.lift' rank hRank.1
  refine ⟨order, ?_⟩
  change ∀ v x y : V,
    rank v < rank x → rank v < rank y → x ≠ y →
      G.Adj v x → G.Adj v y → G.Adj x y
  exact hRank.2

/-- Choosing a simplicial vertex in each nonempty induced subgraph suffices
to construct the elimination order. At each deletion, assign rank zero to
the chosen vertex and shift the remaining ranks up by one. -/
theorem exists_perfectEliminationOrder_of_simplicial_subsets
    [Fintype V] (G : SimpleGraph V)
    (hSimplicial : ∀ S : Finset V, S.Nonempty →
      ∃ v ∈ S, IsSimplicialWithin G (S : Set V) v) :
    ∃ order : LinearOrder V, @IsPerfectEliminationOrder V order G := by
  classical
  have rankOn (S : Finset V) :
      ∃ r : V → ℕ, Set.InjOn r (S : Set V) ∧
        ∀ v ∈ S, ∀ x ∈ S, ∀ y ∈ S, r v < r x → r v < r y →
          x ≠ y → G.Adj v x → G.Adj v y → G.Adj x y := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hS : S.Nonempty
      · obtain ⟨a, ha, haSimp⟩ := hSimplicial S hS
        obtain ⟨r, hr, hLater⟩ := ih (S.erase a) (Finset.erase_ssubset ha)
        let r' (x : V) := if x = a then 0 else r x + 1
        have memErase {x : V} (hx : x ∈ S) (hna : x ≠ a) :
            x ∈ S.erase a := Finset.mem_erase.mpr ⟨hna, hx⟩
        use r'
        constructor
        · intro x hx y hy hxy
          by_cases hxa : x = a <;> by_cases hya : y = a
          · exact hxa.trans hya.symm
          · simp [r', hxa, hya] at hxy
          · simp [r', hxa, hya] at hxy
          · apply hr (memErase hx hxa) (memErase hy hya)
            simpa [r', hxa, hya] using hxy
        · intro v hv x hx y hy hvx hvy hxy hvxAdj hvyAdj
          by_cases hva : v = a
          · subst v
            exact haSimp x hx y hy hxy hvxAdj hvyAdj
          · have hxa : x ≠ a := by
              intro h
              simp [r', h, hva] at hvx
            have hya : y ≠ a := by
              intro h
              simp [r', h, hva] at hvy
            apply hLater v (memErase hv hva) x (memErase hx hxa) y (memErase hy hya)
            · simpa [r', hva, hxa] using hvx
            · simpa [r', hva, hya] using hvy
            · exact hxy
            · exact hvxAdj
            · exact hvyAdj
      · rw [Finset.not_nonempty_iff_eq_empty] at hS
        subst S
        exact ⟨fun _ => 0, by simp [Set.InjOn], by simp⟩
  obtain ⟨r, hInj, hLater⟩ := rankOn Finset.univ
  apply exists_perfectEliminationOrder_of_ranking G r
  exact ⟨fun _ _ h => hInj (Finset.mem_univ _) (Finset.mem_univ _) h,
    fun v x y => hLater v (Finset.mem_univ _) x (Finset.mem_univ _) y (Finset.mem_univ _)⟩

end StructuralRamsey.Girth

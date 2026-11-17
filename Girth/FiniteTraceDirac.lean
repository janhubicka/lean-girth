import Girth.FiniteTraceSeparatorPath
import Girth.FiniteTraceChordality

/-!
# Dirac's theorem and the small trace selection

A minimal separator has two principal components that meet the neighbourhood
of every separator vertex. Two nonadjacent separator vertices would give one
shortest path through each component. The two paths form an induced cycle.
The separator is thus a clique and the finite elimination induction applies.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

private theorem induced_cycle_of_separated_paths {G : SimpleGraph V}
    {A B : Set V} {s t : V}
    (p : InducedPathThrough G A s t) (q : InducedPathThrough G B t s)
    (hCross : ∀ x ∈ A, ∀ y ∈ B, x ≠ y ∧ ¬ G.Adj x y) :
    ∃ k : ℕ, 4 ≤ k ∧ ∃ v : Fin k → V, IsInducedFinCycle G k v := by
  let k := p.length + q.length
  have hp := p.length_ge_two
  have hq := q.length_ge_two
  have hk : 4 ≤ k := by dsimp [k]; omega
  let v (i : Fin k) : V :=
    if i.val < p.length then p.vertex i.val else q.vertex (i.val - p.length)
  have cross_ne (i j : Fin k) (hi : i.val < p.length) (hj : p.length ≤ j.val) :
      p.vertex i.val ≠ q.vertex (j.val - p.length) := by
    have hjlt : j.val - p.length < q.length := by have := j.isLt; dsimp [k] at this; omega
    by_cases hiZero : i.val = 0
    · intro heq
      have hEqEnd : q.vertex q.length = q.vertex (j.val - p.length) :=
        q.finish.trans (p.start.symm.trans (by simpa only [hiZero] using heq))
      have hpos := q.injective_on (show q.length ≤ q.length from le_rfl)
        (show j.val - p.length ≤ q.length from hjlt.le)
        hEqEnd
      omega
    · by_cases hjStart : j.val = p.length
      · intro heq
        have hsub : j.val - p.length = 0 := by omega
        have hEnds : q.vertex 0 = p.vertex p.length := q.start.trans p.finish.symm
        rw [hsub, hEnds] at heq
        have hpos := p.injective_on hi.le (show p.length ≤ p.length from le_rfl) heq
        omega
      · exact (hCross _ (p.internal _ (by omega) hi)
          _ (q.internal _ (by omega) hjlt)).1
  have hvInjective : Function.Injective v := by
    intro i j heq
    apply Fin.ext
    by_cases hi : i.val < p.length <;> by_cases hj : j.val < p.length
    · exact p.injective_on hi.le hj.le (by simpa only [v, ite_eq_left hi, ite_eq_left hj] using heq)
    · exact (cross_ne i j hi (Nat.le_of_not_gt hj)
        (by simpa only [v, ite_eq_left hi, ite_eq_right hj] using heq)).elim
    · exact (cross_ne j i hj (Nat.le_of_not_gt hi)
        (by simpa only [v, ite_eq_left hj, ite_eq_right hi] using heq.symm)).elim
    · have hi' : i.val - p.length ≤ q.length := by have := i.isLt; dsimp [k] at this; omega
      have hj' : j.val - p.length ≤ q.length := by have := j.isLt; dsimp [k] at this; omega
      have h := q.injective_on hi' hj'
        (by simpa only [v, ite_eq_right hi, ite_eq_right hj] using heq)
      omega
  have hvAdj (i j : Fin k) (hij : i.val ≤ j.val) :
      G.Adj (v i) (v j) ↔ (SimpleGraph.cycleGraph k).Adj i j := by
    rw [cycleGraph_adj_iff_of_val_le hk i j hij]
    have hiK := i.isLt
    have hjK := j.isLt
    dsimp [k] at *
    by_cases hj : j.val < p.length
    · have hi : i.val < p.length := lt_of_le_of_lt hij hj
      rw [show v i = p.vertex i.val from ite_eq_left hi,
        show v j = p.vertex j.val from ite_eq_left hj, p.adj_iff _ _ hi.le hj.le]
      omega
    · by_cases hi : i.val < p.length
      · rw [show v i = p.vertex i.val from ite_eq_left hi,
          show v j = q.vertex (j.val - p.length) from ite_eq_right hj]
        have hjLt : j.val - p.length < q.length := by omega
        by_cases hZero : i.val = 0
        · rw [hZero, p.start.trans q.finish.symm,
            q.adj_iff _ _ le_rfl hjLt.le]
          omega
        · by_cases hStart : j.val = p.length
          · have hSub : j.val - p.length = 0 := by omega
            rw [hSub, q.start.trans p.finish.symm, p.adj_iff _ _ hi.le le_rfl]
            omega
          · have hNotAdj := (hCross _ (p.internal _ (by omega) hi)
              _ (q.internal _ (by omega) hjLt)).2
            constructor
            · exact fun h => (hNotAdj h).elim
            · rintro (hConsecutive | ⟨hFirst, _⟩)
              · have hjBeyond : p.length < j.val :=
                  lt_of_le_of_ne (Nat.le_of_not_gt hj) (fun h => hStart h.symm)
                omega
              · exact (hZero hFirst).elim
      · have hi' : i.val - p.length ≤ q.length := by omega
        have hj' : j.val - p.length ≤ q.length := by omega
        rw [show v i = q.vertex (i.val - p.length) from ite_eq_right hi,
          show v j = q.vertex (j.val - p.length) from ite_eq_right hj,
          q.adj_iff _ _ hi' hj']
        omega
  refine ⟨k, hk, v, hvInjective, fun i j => ?_⟩
  rcases le_total i.val j.val with hij | hji
  · exact hvAdj i j hij
  · rw [G.adj_comm, (SimpleGraph.cycleGraph k).adj_comm]
    exact hvAdj j i hji

/-- A minimum separator of a finite induced subgraph of a chordal graph is a clique. -/
theorem minimal_separator_isClique_of_noLongInducedCycles
    {G : SimpleGraph V} (hChordal : NoLongInducedCycles G)
    (T : Finset V) {a b : V} {S : Finset V}
    (ha : a ∈ T) (hb : b ∈ T)
    (hMin : MinimalFor (SeparatesIn G T a b) Finset.card S) :
    G.IsClique (S : Set V) := by
  intro s hs t ht hst
  by_contra hNotAdj
  let R := (T : Set V) \ (S : Set V)
  have neighbourA (z : V) (hz : z ∈ S) :=
    MinimalFor.neighbour_in_separator_component G T hMin ha hz
  have neighbourB (z : V) (hz : z ∈ S) :=
    MinimalFor.neighbour_in_separator_component G T (MinimalFor.separator_symm hMin) hb hz
  obtain ⟨p⟩ := exists_inducedPathThrough_componentIn G R hst hNotAdj
    (neighbourA s hs) (neighbourA t ht)
  obtain ⟨q⟩ := exists_inducedPathThrough_componentIn G R hst.symm
    (fun h => hNotAdj h.symm) (neighbourB t ht) (neighbourB s hs)
  obtain ⟨k, hk, v, hv⟩ := induced_cycle_of_separated_paths p q
    (fun _ hx _ hy => separate_componentsIn hMin.prop.2.2.2 hx hy)
  exact hChordal k hk v hv

/-- Every finite graph with no induced cycle of length at least four has a PEO. -/
theorem exists_perfectEliminationOrder_of_noLongInducedCycles
    [Fintype V] {G : SimpleGraph V} (hChordal : NoLongInducedCycles G) :
    ∃ order : LinearOrder V, @IsPerfectEliminationOrder V order G := by
  classical
  apply exists_perfectEliminationOrder_of_inducedCliqueSeparations G
  intro T hNotClique
  change ¬ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → G.Adj x y at hNotClique
  push Not at hNotClique
  obtain ⟨a, ha, b, hb, hab, hNotAdj⟩ := hNotClique
  obtain ⟨S, hMin⟩ := exists_minimal_separatorIn G T hab hNotAdj
  exact inducedCliqueSeparation_of_minimal_separator G T ha hb hMin.prop
    (minimal_separator_isClique_of_noLongInducedCycles hChordal T ha hb hMin)

end StructuralRamsey.Girth

import Girth.Berge
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-! # Boundary incidence graphs

The equality case of the forest increment is controlled by the bipartite
incidence graph between distinct boundary edges and their vertices.  This file
starts that reduction: the incidence graph is explicitly two-coloured, hence
every closed walk has even length.  The next layer extracts a Berge cycle from
an incidence cycle.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- Bipartite incidence graph of a labelled family of hyperedges. -/
def boundaryIncidenceGraph (edge : E → Set W) : SimpleGraph (E ⊕ W) where
  Adj a b :=
    match a, b with
    | .inl e, .inr x => x ∈ edge e
    | .inr x, .inl e => x ∈ edge e
    | _, _ => False
  symm := ⟨by
    intro a b
    cases a <;> cases b <;> simp_all⟩
  loopless := ⟨by
    intro a
    cases a <;> simp⟩

@[simp]
theorem boundaryIncidenceGraph_adj_left_right
    (edge : E → Set W) (e : E) (x : W) :
    (boundaryIncidenceGraph edge).Adj (Sum.inl e) (Sum.inr x) ↔
      x ∈ edge e :=
  Iff.rfl

@[simp]
theorem boundaryIncidenceGraph_adj_right_left
    (edge : E → Set W) (e : E) (x : W) :
    (boundaryIncidenceGraph edge).Adj (Sum.inr x) (Sum.inl e) ↔
      x ∈ edge e :=
  Iff.rfl

@[simp]
theorem boundaryIncidenceGraph_not_adj_left_left
    (edge : E → Set W) (e f : E) :
    ¬(boundaryIncidenceGraph edge).Adj (Sum.inl e) (Sum.inl f) := by
  simp [boundaryIncidenceGraph]

@[simp]
theorem boundaryIncidenceGraph_not_adj_right_right
    (edge : E → Set W) (x y : W) :
    ¬(boundaryIncidenceGraph edge).Adj (Sum.inr x) (Sum.inr y) := by
  simp [boundaryIncidenceGraph]

/-- The canonical bipartite colouring: edge-nodes and vertex-nodes receive
opposite Boolean colours. -/
def boundaryIncidenceColoring
    (edge : E → Set W) :
    (boundaryIncidenceGraph edge).Coloring Bool :=
  SimpleGraph.Coloring.mk
    (fun z => match z with
      | .inl _ => false
      | .inr _ => true) <| by
    intro a b hab
    cases a <;> cases b <;>
      simp [boundaryIncidenceGraph] at hab ⊢

@[simp]
theorem boundaryIncidenceColoring_inl
    (edge : E → Set W) (e : E) :
    boundaryIncidenceColoring edge (Sum.inl e) = false :=
  rfl

@[simp]
theorem boundaryIncidenceColoring_inr
    (edge : E → Set W) (x : W) :
    boundaryIncidenceColoring edge (Sum.inr x) = true :=
  rfl

/-- Every closed incidence walk has even length. -/
theorem boundaryIncidence_closedWalk_even
    (edge : E → Set W)
    {z : E ⊕ W}
    (p : (boundaryIncidenceGraph edge).Walk z z) :
    Even p.length := by
  exact
    ((boundaryIncidenceColoring edge).even_length_iff_congr p).2
      (Iff.rfl)

/-- In particular every incidence cycle has even length. -/
theorem boundaryIncidence_cycle_even
    (edge : E → Set W)
    {z : E ⊕ W}
    {p : (boundaryIncidenceGraph edge).Walk z z}
    (_hp : p.IsCycle) :
    Even p.length :=
  boundaryIncidence_closedWalk_even edge p


/-- In a closed incidence walk based at an edge-node, every even position
(before the endpoint) is again an edge-node. -/
theorem boundaryIncidence_getVert_even_left
    (edge : E → Set W)
    {e0 : E}
    (p : (boundaryIncidenceGraph edge).Walk (Sum.inl e0) (Sum.inl e0))
    {k : ℕ}
    (hk : k ≤ p.length)
    (heven : Even k) :
    ∃ e : E, p.getVert k = Sum.inl e := by
  have htakeEven : Even (p.take k).length := by
    simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hk] using heven
  have hsame :=
    ((boundaryIncidenceColoring edge).even_length_iff_congr
      (p.take k)).1 htakeEven
  cases h : p.getVert k with
  | inl e =>
      exact ⟨e, rfl⟩
  | inr x =>
      exfalso
      rw [h] at hsame
      simp at hsame

/-- In a closed incidence walk based at an edge-node, every odd position
(before the endpoint) is a vertex-node. -/
theorem boundaryIncidence_getVert_odd_right
    (edge : E → Set W)
    {e0 : E}
    (p : (boundaryIncidenceGraph edge).Walk (Sum.inl e0) (Sum.inl e0))
    {k : ℕ}
    (hk : k ≤ p.length)
    (hodd : Odd k) :
    ∃ x : W, p.getVert k = Sum.inr x := by
  have htakeOdd : Odd (p.take k).length := by
    simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hk] using hodd
  have hdiff :=
    ((boundaryIncidenceColoring edge).odd_length_iff_not_congr
      (p.take k)).1 htakeOdd
  cases h : p.getVert k with
  | inl e =>
      exfalso
      rw [h] at hdiff
      simp at hdiff
  | inr x =>
      exact ⟨x, rfl⟩

end StructuralRamsey.Girth

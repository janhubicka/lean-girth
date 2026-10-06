import Girth.BoundaryIncidence

/-! # Incidence cycles give Berge cycles

For an injectively labelled family of hyperedges, a simple cycle in the
bipartite edge-vertex incidence graph alternates distinct edge nodes and
distinct vertex nodes. Reading every second node therefore gives a Berge cycle.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- An incidence cycle based at an edge-node yields a Berge cycle on the
underlying labelled edge family. -/
noncomputable def bergeCycleOfBoundaryIncidenceCycleLeft
    (edge : E → Set W)
    (hEdgeInj : Function.Injective edge)
    {e0 : E}
    (p : (boundaryIncidenceGraph edge).Walk
      (Sum.inl e0) (Sum.inl e0))
    (hp : p.IsCycle) :
    BergeCycle (Set.range edge) := by
  classical
  have hEven : Even p.length :=
    boundaryIncidence_cycle_even edge hp
  let m : ℕ := p.length / 2
  have hlen : p.length = 2 * m := by
    have htwo : 2 * (p.length / 2) = p.length :=
      Nat.two_mul_div_two_of_even hEven
    simpa [m] using htwo.symm
  have hm2 : 2 ≤ m := by
    have h3 := hp.three_le_length
    omega
  have hEdgePos (i : Fin m) :
      ∃ e : E, p.getVert (2 * i.1) = Sum.inl e := by
    apply boundaryIncidence_getVert_even_left edge p
    · rw [hlen]
      omega
    · exact even_two_mul i.1
  have hVertPos (i : Fin m) :
      ∃ x : W, p.getVert (2 * i.1 + 1) = Sum.inr x := by
    apply boundaryIncidence_getVert_odd_right edge p
    · rw [hlen]
      omega
    · exact odd_two_mul_add_one i.1
  let edgeLabel : Fin m → E :=
    fun i => Classical.choose (hEdgePos i)
  let vertexLabel : Fin m → W :=
    fun i => Classical.choose (hVertPos i)
  have hEdgeAt (i : Fin m) :
      p.getVert (2 * i.1) = Sum.inl (edgeLabel i) :=
    Classical.choose_spec (hEdgePos i)
  have hVertAt (i : Fin m) :
      p.getVert (2 * i.1 + 1) = Sum.inr (vertexLabel i) :=
    Classical.choose_spec (hVertPos i)
  have hEdgeLabelInj : Function.Injective edgeLabel := by
    intro i j hij
    have hpos :
        p.getVert (2 * i.1) = p.getVert (2 * j.1) := by
      rw [hEdgeAt i, hEdgeAt j, hij]
    have hiBound : 2 * i.1 ≤ p.length - 1 := by
      rw [hlen]
      omega
    have hjBound : 2 * j.1 ≤ p.length - 1 := by
      rw [hlen]
      omega
    have hidx :=
      hp.getVert_injOn' hiBound hjBound hpos
    apply Fin.ext
    omega
  have hVertexLabelInj : Function.Injective vertexLabel := by
    intro i j hij
    have hpos :
        p.getVert (2 * i.1 + 1) =
          p.getVert (2 * j.1 + 1) := by
      rw [hVertAt i, hVertAt j, hij]
    have hiBound : 2 * i.1 + 1 ≤ p.length - 1 := by
      rw [hlen]
      omega
    have hjBound : 2 * j.1 + 1 ≤ p.length - 1 := by
      rw [hlen]
      omega
    have hidx :=
      hp.getVert_injOn' hiBound hjBound hpos
    apply Fin.ext
    omega
  have hCyclicGetVert (i : Fin m) :
      p.getVert (2 * (cyclicSucc i).1) =
        p.getVert (2 * i.1 + 2) := by
    by_cases hnext : i.1 + 1 < m
    · have hmod :
          (i.1 + 1) % m = i.1 + 1 :=
        Nat.mod_eq_of_lt hnext
      change
        p.getVert (2 * ((i.1 + 1) % m)) =
          p.getVert (2 * i.1 + 2)
      rw [hmod]
      congr 1
    · have hilast : i.1 + 1 = m := by
        omega
      have hcyc0 : (cyclicSucc i).1 = 0 := by
        simp [cyclicSucc, hilast, hm2]
      have hlast : 2 * i.1 + 2 = p.length := by
        rw [hlen]
        omega
      rw [hcyc0, hlast, p.getVert_zero, p.getVert_length]
  refine
    { length := m
      hlength := hm2
      edge := fun i => edge (edgeLabel i)
      vertex := vertexLabel
      edge_mem := ?_
      edge_injective := ?_
      vertex_injective := hVertexLabelInj
      left_mem := ?_
      right_mem := ?_ }
  · intro i
    exact ⟨edgeLabel i, rfl⟩
  · intro i j hij
    exact hEdgeLabelInj (hEdgeInj hij)
  · intro i
    have hadj :=
      p.adj_getVert_succ
        (show 2 * i.1 < p.length by
          rw [hlen]
          omega)
    rw [hEdgeAt i, hVertAt i] at hadj
    exact
      (boundaryIncidenceGraph_adj_left_right
        edge (edgeLabel i) (vertexLabel i)).mp hadj
  · intro i
    have hadj :=
      p.adj_getVert_succ
        (show 2 * i.1 + 1 < p.length by
          rw [hlen]
          omega)
    have hnext := hCyclicGetVert i
    rw [hVertAt i, ← hnext, hEdgeAt (cyclicSucc i)] at hadj
    exact
      (boundaryIncidenceGraph_adj_right_left
        edge (edgeLabel (cyclicSucc i)) (vertexLabel i)).mp hadj


/-- Any simple cycle in the boundary incidence graph yields a Berge cycle.
If the cycle is based at a vertex-node, rotate it to its second node, which
must be an edge-node by bipartiteness. -/
noncomputable def bergeCycleOfBoundaryIncidenceCycle
    (edge : E → Set W)
    (hEdgeInj : Function.Injective edge)
    {z : E ⊕ W}
    (p : (boundaryIncidenceGraph edge).Walk z z)
    (hp : p.IsCycle) :
    BergeCycle (Set.range edge) := by
  classical
  cases z with
  | inl e0 =>
      exact
        bergeCycleOfBoundaryIncidenceCycleLeft
          edge hEdgeInj p hp
  | inr x =>
      have hnon : ¬p.Nil := hp.not_nil
      have hadj :
          (boundaryIncidenceGraph edge).Adj
            (Sum.inr x) p.snd :=
        p.adj_snd hnon
      cases hsnd : p.snd with
      | inl e =>
          have hsupp : Sum.inl e ∈ p.support := by
            have htail := p.snd_mem_tail_support hnon
            have hall : p.snd ∈ p.support :=
              List.mem_of_mem_tail htail
            simpa [hsnd] using hall
          let q := p.rotate (Sum.inl e) hsupp
          have hq : q.IsCycle := hp.rotate hsupp
          exact
            bergeCycleOfBoundaryIncidenceCycleLeft
              edge hEdgeInj q hq
      | inr y =>
          exfalso
          have hbad :
              (boundaryIncidenceGraph edge).Adj
                (Sum.inr x) (Sum.inr y) := by
            simpa [hsnd] using hadj
          exact
            (boundaryIncidenceGraph_not_adj_right_right
              edge x y hbad)

end StructuralRamsey.Girth

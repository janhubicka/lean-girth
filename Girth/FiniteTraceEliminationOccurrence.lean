import Girth.FiniteTraceEliminationParent
import Mathlib.Order.Preorder.Finite

/-!
# Connected occurrences in the elimination-parent graph

For a finite graph equipped with a perfect elimination order, connect
each vertex v that has a later neighbour to its LEAST later neighbour.
Every occurrence of x in the elimination bag at v has a parent chain
to the bag indexed by x, and all intermediate bags still contain x.

This module proves the complete running-intersection condition of the
parent graph without assuming that the parent graph is a tree or
invoking any unproved chordal-graph theorem.  The proof avoids
recursive parent iteration: a maximum bad index would have a strictly
larger parent which is not bad.

The separate tasks are to prove acyclicity of the parent graph,
connect its components (without damaging occurrence connectivity),
and delete contained/duplicate bags.  No claim that a perfect
elimination order exists is made here.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

/-- Edges of the elimination-parent graph: each vertex with a later
neighbour is joined to its least later neighbour. -/
noncomputable def eliminationParentGraph
    [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) : SimpleGraph V where
  Adj v w :=
    (∃ h : (laterNeighbors G v).Nonempty,
      w = (laterNeighbors G v).min' h) ∨
    (∃ h : (laterNeighbors G w).Nonempty,
      v = (laterNeighbors G w).min' h)
  symm := by
    intro v w h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  loopless := by
    intro v h
    rcases h with ⟨hN, hv⟩ | ⟨hN, hv⟩
    · have hlt : v < (laterNeighbors G v).min' hN :=
        (min_laterNeighbor_specs G v hN).1
      exact (ne_of_gt hlt) hv.symm
    · have hlt : v < (laterNeighbors G v).min' hN :=
        (min_laterNeighbor_specs G v hN).1
      exact (ne_of_gt hlt) hv.symm

/-- The chosen parent edge exists in the elimination-parent graph. -/
theorem eliminationParentGraph_parent_adj
    [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (v : V)
    (hN : (laterNeighbors G v).Nonempty) :
    (eliminationParentGraph G).Adj
      v ((laterNeighbors G v).min' hN) := by
  exact Or.inl ⟨hN, rfl⟩

/-- The bags containing a vertex form a connected subgraph of the
elimination-parent graph, without requiring global connectivity or
acyclicity of that graph. -/
theorem eliminationParentGraph_bag_occurrences_preconnected
    [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hPEO : IsPerfectEliminationOrder G)
    (x : V) :
    ((eliminationParentGraph G).induce
      {v : V | x ∈ laterNeighborBag G v}).Preconnected := by
  classical
  let occ : Set V := {v : V | x ∈ laterNeighborBag G v}
  let H := eliminationParentGraph G
  let xOcc : occ := ⟨x, Or.inl rfl⟩
  have reachAll :
      ∀ v : occ,
        (H.induce occ).Reachable v xOcc := by
    intro v
    by_contra hNot
    let bad : Set occ :=
      {u | ¬ (H.induce occ).Reachable u xOcc}
    have hBad : bad.Nonempty := ⟨v, hNot⟩
    have hBadFinite : bad.Finite := Set.toFinite bad
    obtain ⟨u, huBad, huMax⟩ :=
      Set.Finite.exists_maximalFor
        (fun a : occ => a.1) bad hBadFinite hBad
    have huNe : u.1 ≠ x := by
      intro heq
      have hEq : u = xOcc := Subtype.ext heq
      apply huBad
      simpa [hEq] using
        (SimpleGraph.Reachable.refl xOcc :
          (H.induce occ).Reachable xOcc xOcc)
    have huIn : u.1 < x ∧ G.Adj u.1 x := by
      rcases u.2 with hEq | h
      · exact (huNe hEq.symm).elim
      · exact h
    have hN : (laterNeighbors G u.1).Nonempty := by
      exact ⟨x, (mem_laterNeighbors_iff G u.1 x).mpr huIn⟩
    let p : V := (laterNeighbors G u.1).min' hN
    have hup : u.1 < p :=
      (min_laterNeighbor_specs G u.1 hN).1
    have hxP : x ∈ laterNeighborBag G p := by
      exact laterNeighbor_mem_parentBag G hPEO u.1 x
        hN huIn.1 huIn.2
    let pOcc : occ := ⟨p, hxP⟩
    have hpNotBad : pOcc ∉ bad := by
      intro hpBad
      have hpLeU : p ≤ u.1 :=
        huMax pOcc hpBad (le_of_lt hup)
      exact (not_le_of_gt hup) hpLeU
    have hpReach :
        (H.induce occ).Reachable pOcc xOcc := by
      by_contra hpNo
      exact hpNotBad hpNo
    have hAdj :
        (H.induce occ).Adj u pOcc := by
      change (eliminationParentGraph G).Adj u.1 p
      exact eliminationParentGraph_parent_adj G u.1 hN
    exact huBad (hAdj.reachable.trans hpReach)
  intro v w
  exact (reachAll v).trans (reachAll w).symm

/-- A larger neighbour in the elimination-parent graph must be
the uniquely chosen least later neighbour, never a reverse parent
edge.  The two nonempty proofs are propositionally equal. -/
theorem eliminationParentGraph_greater_is_parent
    [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {v w : V}
    (hAdj : (eliminationParentGraph G).Adj v w)
    (hvw : v < w) :
    ∃ hN : (laterNeighbors G v).Nonempty,
      w = (laterNeighbors G v).min' hN := by
  rcases hAdj with ⟨hN, hw⟩ | ⟨hN, hv⟩
  · exact ⟨hN, hw⟩
  · have hwv : w < v := by
      calc
        w < (laterNeighbors G w).min' hN :=
          (min_laterNeighbor_specs G w hN).1
        _ = v := hv.symm
    exact (lt_asymm hvw hwv).elim

/-- Every vertex has at most one STRICTLY LARGER neighbour in
the elimination-parent graph.  This is the key finite-forest
acyclicity condition: a cycle's least vertex would have two. -/
theorem eliminationParentGraph_unique_greater_neighbour
    [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {v w u : V}
    (hw : (eliminationParentGraph G).Adj v w)
    (hu : (eliminationParentGraph G).Adj v u)
    (hvw : v < w) (hvu : v < u) :
    w = u := by
  obtain ⟨hwN, hwp⟩ :=
    eliminationParentGraph_greater_is_parent G hw hvw
  obtain ⟨huN, hup⟩ :=
    eliminationParentGraph_greater_is_parent G hu hvu
  calc
    w = (laterNeighbors G v).min' hwN := hwp
    _ = (laterNeighbors G v).min' huN := by
      rw [Subsingleton.elim hwN huN]
    _ = u := hup.symm


end StructuralRamsey.Girth

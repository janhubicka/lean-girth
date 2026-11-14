import Girth.TrainColouredOwnerExactColourTransfer
import Girth.Berge
import Mathlib.Tactic

/-!
# Projection of Berge cycles through the physical edge-owner splitting

This lemma completes the pure girth argument of the existing selected
coloured-edge splitting construction. Distinct new physical edges are
identified with distinct old physical edges. Their common vertices
necessarily have allowed predicates, hence have unmodified names;
a Berge cycle therefore projects with all connectors distinct.

DRAFT: exact-head Lean/kernel/axioms check NOT run.
-/

namespace StructuralRamsey.Girth

universe v

namespace ColouredEdgeOwnerSplit

variable {V I : Type v} (H : ColouredEdgeOwnerSplit V I)

/-- The physical owner split preserves every old strict Berge-girth bound.
No selected-copy or target-label hypothesis is required. -/
theorem splitPhysicalEdges_girthGT
    (g : ℕ) (hOld : GirthGT H.edges g) :
    GirthGT H.splitPhysicalEdges g := by
  classical
  rintro ⟨c, hcLen⟩
  have hChoice (i : Fin c.length) :
      ∃ e : H.OldEdge, c.edge i = H.splitEdge e := c.edge_mem i
  choose e he using hChoice
  let oldEdge : Fin c.length → Set V := fun i => (e i).1
  have hOldMem (i : Fin c.length) : oldEdge i ∈ H.edges := (e i).2
  have hEdgeInj : Function.Injective oldEdge := by
    intro i j hij
    have heq : e i = e j := Subtype.ext hij
    apply c.edge_injective
    calc
      c.edge i = H.splitEdge (e i) := he i
      _ = H.splitEdge (e j) := congrArg H.splitEdge heq
      _ = c.edge j := (he j).symm
  have hNextNe (i : Fin c.length) : i ≠ cyclicSucc i := by
    intro h
    have hval := congrArg Fin.val h
    have hn : 1 < c.length := by omega
    have hmod : (i.val + 1) % c.length ≠ i.val := by
      by_cases hi : i.val + 1 < c.length
      · rw [Nat.mod_eq_of_lt hi]
        omega
      · have hlast : i.val + 1 = c.length := by omega
        rw [hlast, Nat.mod_self]
        omega
    exact hmod (by simpa [cyclicSucc] using hval)
  have hEdgeNe (i : Fin c.length) : e i ≠ e (cyclicSucc i) := by
    intro heq
    apply hNextNe i
    apply c.edge_injective
    calc
      c.edge i = H.splitEdge (e i) := he i
      _ = H.splitEdge (e (cyclicSucc i)) := congrArg H.splitEdge heq
      _ = c.edge (cyclicSucc i) := (he _).symm
  have hConnector (i : Fin c.length) :
      ∃ x : V, H.predicate x ∈ H.allowed ∧ c.vertex i = Sum.inl x := by
    have hi : c.vertex i ∈ H.splitEdge (e i) := by
      rw [← he i]
      exact c.left_mem i
    have hj : c.vertex i ∈ H.splitEdge (e (cyclicSucc i)) := by
      rw [← he (cyclicSucc i)]
      exact c.right_mem i
    exact H.intersection_only_allowed (e i) (e (cyclicSucc i))
      (hEdgeNe i) (c.vertex i) hi hj
  let oldVertex : Fin c.length → V := fun i => H.project (c.vertex i)
  have hVertexInj : Function.Injective oldVertex := by
    intro i j hij
    obtain ⟨x, _, hx⟩ := hConnector i
    obtain ⟨y, _, hy⟩ := hConnector j
    have hxy : x = y := by
      change H.project (c.vertex i) = H.project (c.vertex j) at hij
      rw [hx, hy] at hij
      simpa [ColouredEdgeOwnerSplit.project] using hij
    apply c.vertex_injective
    rw [hx, hy, hxy]
  have hLeft (i : Fin c.length) : oldVertex i ∈ oldEdge i := by
    have hp : H.project (c.vertex i) ∈
        H.project '' H.splitEdge (e i) :=
      ⟨c.vertex i, by rw [← he i]; exact c.left_mem i, rfl⟩
    rw [H.projection_splitEdge] at hp
    exact hp
  have hRight (i : Fin c.length) :
      oldVertex i ∈ oldEdge (cyclicSucc i) := by
    have hp : H.project (c.vertex i) ∈
        H.project '' H.splitEdge (e (cyclicSucc i)) :=
      ⟨c.vertex i, by rw [← he (cyclicSucc i)]; exact c.right_mem i, rfl⟩
    rw [H.projection_splitEdge] at hp
    exact hp
  let cOld : BergeCycle H.edges := {
    length := c.length
    hlength := c.hlength
    edge := oldEdge
    vertex := oldVertex
    edge_mem := hOldMem
    edge_injective := hEdgeInj
    vertex_injective := hVertexInj
    left_mem := hLeft
    right_mem := hRight
  }
  exact hOld ⟨cOld, hcLen⟩

#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.splitPhysicalEdges_girthGT

end ColouredEdgeOwnerSplit
end StructuralRamsey.Girth

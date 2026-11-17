import Girth.Berge

set_option autoImplicit false

namespace StructuralRamsey.Girth

universe v

private theorem shortCyclic_neighbours (n : ℕ) (hn : 2 ≤ n) (hThree : n ≤ 3)
    (i j : Fin n) : i = j ∨ cyclicSucc i = j ∨ cyclicSucc j = i := by
  have hCases : n = 2 ∨ n = 3 := by omega
  rcases hCases with h | h
  · subst n
    revert i j
    decide
  · subst n
    revert i j
    decide

/-- An edge-injective projection that is injective on each edge preserves
girth greater than three. Two connectors of a short cycle share an edge. -/
theorem girthGT_three_of_edgeProjection
    {X Y : Type v} {E : Set (Set X)} {F : Set (Set Y)} (project : X → Y)
    (hMap : ∀ e ∈ E, project '' e ∈ F)
    (hEdge : Set.InjOn (fun e : Set X => project '' e) E)
    (hVertex : ∀ e ∈ E, Set.InjOn project e)
    (hGirth : GirthGT F 3) : GirthGT E 3 := by
  rintro ⟨cycle, hLength⟩
  apply hGirth
  refine ⟨{
    length := cycle.length
    hlength := cycle.hlength
    edge := fun i => project '' cycle.edge i
    vertex := fun i => project (cycle.vertex i)
    edge_mem := fun i => hMap _ (cycle.edge_mem i)
    edge_injective := fun i j h =>
      cycle.edge_injective (hEdge (cycle.edge_mem i) (cycle.edge_mem j) h)
    vertex_injective := ?_
    left_mem := fun i => ⟨_, cycle.left_mem i, rfl⟩
    right_mem := fun i => ⟨_, cycle.right_mem i, rfl⟩
  }, hLength⟩
  intro i j h
  rcases shortCyclic_neighbours _ cycle.hlength hLength i j with hi | hi | hj
  · exact hi
  · have hi' : cycle.vertex i ∈ cycle.edge j := hi ▸ cycle.right_mem i
    exact cycle.vertex_injective (hVertex _ (cycle.edge_mem j) hi' (cycle.left_mem j) h)
  · have hj' : cycle.vertex j ∈ cycle.edge i := hj ▸ cycle.right_mem j
    exact cycle.vertex_injective (hVertex _ (cycle.edge_mem i) (cycle.left_mem i) hj' h)

#print axioms StructuralRamsey.Girth.girthGT_three_of_edgeProjection

end StructuralRamsey.Girth

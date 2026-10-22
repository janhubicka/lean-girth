import Girth.TrainCyclicRestriction

/-!
# Regression examples for cyclic restriction

These are literal typed big cycles with physical singleton edges.  Wagon
0 contains vertices 0 and 3; wagon 1 contains vertices 1 and 2.  The
five-position source is W0, x0, x1, x2, x3.

The first restriction deletes W0.  Its two source A2 contacts survive
across the cyclic wrap and must become an A3 window.  The second retains
W0 and its two distinct vertex neighbours, testing the nonedge clause of
A2.  Source and output have different designated-label types.
-/

namespace StructuralRamsey.Girth.OrderOneData
namespace CyclicRestrictionRegression

def data (labels : ℕ) : OrderOneData (Fin 4) (Fin 4) (Fin labels) (Fin 2) where
  edgeCarrier e := {e}
  copyCarrier _ := Set.univ
  copyEdges _ := Set.univ
  parent e := if e = 0 ∨ e = 3 then 0 else 1

private theorem designated_incident (labels : ℕ) (i : Fin labels)
    (q : Fin 4 ⊕ Fin 2) : (data labels).Incident (Sum.inl i) q := by
  cases q with
  | inl x => exact Set.mem_univ x
  | inr p =>
      fin_cases p
      · exact ⟨0, Set.mem_univ _, rfl⟩
      · exact ⟨1, Set.mem_univ _, rfl⟩

def source : (data 5).BigCycle 5 where
  length_ge_two := by decide
  label := Sum.inl
  connector := ![Sum.inr 0, Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3]
  adjacent_ne := by decide
  connector_injective := by decide
  left_incident := fun i => designated_incident 5 i _
  right_incident := fun i => designated_incident 5 (cyclicSucc i) _

theorem source_acceptable : source.Acceptable := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro _
    exact ⟨0, trivial⟩
  · intro i p hi j hj
    obtain ⟨x, hx, hpx⟩ := hj
    obtain ⟨e, hep, hxe⟩ := hpx
    have hxe' : x = e := hxe
    subst e
    fin_cases i <;> fin_cases p <;> simp [source] at hi
    fin_cases j <;> fin_cases x <;>
      simp_all [source, data, cyclicSucc, trainCyclicPred]
  · intro i p x y _ hx hy hDifferent _ _ hPair
    obtain ⟨e, hxe, hye⟩ := hPair
    have hxe' : x = e := hxe
    have hye' : y = e := hye
    have hxy : x = y := hxe'.trans hye'.symm
    apply hDifferent
    apply source.connector_injective
    exact hx.trans ((congrArg (Sum.inl : Fin 4 → Fin 4 ⊕ Fin 2) hxy).trans hy.symm)
  · intro p hAbsent
    fin_cases p
    · exact False.elim (hAbsent 0 rfl)
    · clear hAbsent
      refine ⟨(2 : Fin 5), ?_⟩
      intro j hj
      obtain ⟨x, hx, hpx⟩ := hj
      obtain ⟨e, hep, hxe⟩ := hpx
      have hxe' : x = e := hxe
      subst e
      fin_cases j <;> fin_cases x <;>
        simp [source, data, cyclicSucc] at hx hep ⊢

def keepVertices : Fin 4 ↪o Fin 5 where
  toFun j := j.succ
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change i.val + 1 = j.val + 1 at hv
    omega
  map_rel_iff' := by
    intro i j
    change i.val + 1 ≤ j.val + 1 ↔ i.val ≤ j.val
    omega

def vertices : (data 4).BigCycle 4 :=
  source.restrictConnectorWord (D' := data 4) (by decide) keepVertices
    id id Sum.inl (fun j => Sum.inl j)
    (by decide) (by decide)
    (fun j => designated_incident 4 j _)
    (fun j => designated_incident 4 (cyclicSucc j) _)

def verticesMap : source.RestrictionMap vertices where
  position := keepVertices
  vertex := id
  wagon := id
  vertex_injective := fun _ _ h => h
  wagon_injective := fun _ _ h => h
  connector_eq := by decide
  contact := by
    intro p j x _ hx
    exact hx
  pair_reflect := by
    intro j p x y _ _ _ _ _ _ h
    exact h

/-- This uses the deleted-source-wagon branch of A3, including its wrap. -/
theorem vertices_acceptable : vertices.Acceptable :=
  verticesMap.acceptable source_acceptable (by
    intro _
    exact ⟨0, trivial⟩)

example : vertices.twiceOrder ≤ source.twiceOrder := verticesMap.twiceOrder_le

example : vertices.twiceOrder = 8 ∧ source.twiceOrder = 8 := by decide

example : ∀ j : Fin 4, keepVertices j ≠ (0 : Fin 5) :=
  verticesMap.source_wagon_deleted 0 (by decide) 0 (by decide)

/-- The two contacts of the deleted source wagon are exactly the output
last and first positions, not two positions in increasing linear order. -/
example : ∀ j : Fin 4, vertices.InWagonAt 0 j ↔ j = 3 ∨ j = 0 := by
  simp only [BigCycle.InWagonAt, WagonVertex, vertices,
    BigCycle.restrictConnectorWord, data, Set.mem_singleton_iff] <;> decide

def keepWagonAndSides : Fin 3 ↪o Fin 5 where
  toFun := ![0, 1, 4]
  inj' := by decide
  map_rel_iff' := by decide

def wagonAndSides : (data 3).BigCycle 3 :=
  source.restrictConnectorWord (D' := data 3) (by decide) keepWagonAndSides
    id id Sum.inl ![Sum.inr 0, Sum.inl 0, Sum.inl 3]
    (by decide) (by decide)
    (fun j => designated_incident 3 j _)
    (fun j => designated_incident 3 (cyclicSucc j) _)

def wagonAndSidesMap : source.RestrictionMap wagonAndSides where
  position := keepWagonAndSides
  vertex := id
  wagon := id
  vertex_injective := fun _ _ h => h
  wagon_injective := fun _ _ h => h
  connector_eq := by decide
  contact := by
    intro p j x _ hx
    exact hx
  pair_reflect := by
    intro j p x y _ _ _ _ _ _ h
    exact h

/-- This uses the nonvacuous, distinct-neighbour no-common-edge clause. -/
theorem wagonAndSides_acceptable : wagonAndSides.Acceptable :=
  wagonAndSidesMap.acceptable source_acceptable (by
    intro _
    exact ⟨0, trivial⟩)

example : wagonAndSides.twiceOrder = 4 := by decide

example : wagonAndSides.twiceOrder ≤ source.twiceOrder :=
  wagonAndSidesMap.twiceOrder_le

example : trainCyclicPred (0 : Fin 3) ≠ cyclicSucc 0 := by decide

example : ¬ (data 3).PairEdge (3 : Fin 4) 0 := by
  simp only [PairEdge, data, Set.mem_singleton_iff] <;> decide

end CyclicRestrictionRegression
end StructuralRamsey.Girth.OrderOneData

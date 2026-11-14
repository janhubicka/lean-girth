import Girth.ForestAllSupportGirth
import Girth.RestrictedForestGirth
import Girth.ForestCarrierCorner

/-!
# Acyclic edge traces of a forest: Track 2 candidate

A forest member can meet the active subsystem in no vertices, one
vertex, or exactly one active support edge. Retain that edge as the
member's only trace edge. This produces another forest with each
member carrying at most one edge. The established girth-of-a-forest-
union theorem then excludes short cycles in the selected active
edges.

This file is a source candidate for the revised manuscript's
`lem:foresttracegirth`. It was not locally compiled in this session
and MUST NOT be treated as a validation certificate until a focused
build and `#print axioms` succeed.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- Restrict the carrier to S and retain only H-edges entirely inside
that trace. Unlike `restrictCarrier`, this keeps the possible common
trace edge, so the join-tree intersection property survives. -/
def HypergraphPiece.traceWithEdges
    (F : HypergraphPiece W) (S : Set W)
    (H : Set (Set W)) : HypergraphPiece W where
  carrier := F.carrier ∩ S
  edges := {e | e ∈ H ∧ e ⊆ F.carrier ∩ S}
  edge_subset_carrier := by
    intro e he
    exact he.2

/-- A finite join-tree forest whose member traces are singletons or
whole edges of a linear H has an acyclic union of all trace edges.
No assumption that the original member edges have high girth is
needed: every *trace piece* has at most one edge. -/
theorem girthGT_union_of_forest_edge_traces
    [Fintype I]
    (F : I → HypergraphPiece W)
    (hForest : ForestOfCopies F)
    (S : Set W) (H : Set (Set W))
    (hLinear : LinearEdgeSet H)
    (hEdgeBig : ∀ e : Set W, e ∈ H → ¬ e.Subsingleton)
    (hTrace : ∀ i : I,
      ((F i).carrier ∩ S).Subsingleton ∨
        ∃ e : Set W, e ∈ H ∧ (F i).carrier ∩ S = e)
    (g : ℕ) :
    GirthGT
      (⋃ i : I, (HypergraphPiece.traceWithEdges (F i) S H).edges)
      g := by
  classical
  let T : I → HypergraphPiece W :=
    fun i => (F i).traceWithEdges S H
  have hMem (i : I) (e : Set W) :
      e ∈ (T i).edges ↔ e ∈ H ∧ e ⊆ (T i).carrier :=
    Iff.rfl
  have hTraceT (i : I) :
      (T i).carrier.Subsingleton ∨
        ∃ e : Set W, e ∈ H ∧ (T i).carrier = e :=
    hTrace i
  have hAllowed : PairwiseAllowed T := by
    intro i j hij
    by_cases hSmall :
        ((T i).carrier ∩ (T j).carrier).Subsingleton
    · exact Or.inl hSmall
    · have hiNot : ¬ (T i).carrier.Subsingleton := by
        intro h
        apply hSmall
        intro x hx y hy
        exact h hx.1 hy.1
      have hjNot : ¬ (T j).carrier.Subsingleton := by
        intro h
        apply hSmall
        intro x hx y hy
        exact h hx.2 hy.2
      obtain ⟨ei, hei, hEi⟩ := (hTraceT i).resolve_left hiNot
      obtain ⟨ej, hej, hEj⟩ := (hTraceT j).resolve_left hjNot
      have heq : ei = ej := by
        by_contra hne
        apply hSmall
        rw [hEi, hEj]
        exact hLinear hei hej hne
      have hEj' : (T j).carrier = ei :=
        hEj.trans heq.symm
      refine Or.inr ⟨ei, ?_, ?_, ?_⟩
      · exact (hMem i ei).2
          ⟨hei, by rw [hEi]; exact Set.Subset.rfl⟩
      · exact (hMem j ei).2
          ⟨hei, by rw [hEj']; exact Set.Subset.rfl⟩
      · rw [hEi, hEj']
        exact Set.inter_self ei
  have hTraceForest : ForestOfCopies T := by
    refine ⟨hAllowed, ?_⟩
    rcases hForest.2 with hEmpty | ⟨J⟩
    · exact Or.inl hEmpty
    · refine Or.inr ⟨{
        tree := J.tree
        isTree := J.isTree
        running := ?_
      }⟩
      intro x
      have hOcc :
          {i : I | x ∈ (T i).carrier} =
            {i : I |
              x ∈ ((F i).restrictCarrier S).carrier} := by
        ext i
        rfl
      rw [hOcc]
      exact (J.restrictCarriers S).running x
  have hEachSmall (i : I) : (T i).edges.Subsingleton := by
    intro e he f hf
    obtain ⟨heH, heSub⟩ := (hMem i e).mp he
    obtain ⟨hfH, hfSub⟩ := (hMem i f).mp hf
    rcases hTraceT i with hSmall | ⟨t, htH, hCarrier⟩
    · have heSmall : e.Subsingleton := by
        intro x hx y hy
        exact hSmall (heSub hx) (heSub hy)
      exact (hEdgeBig e heH heSmall).elim
    · have het : e = t := by
        by_contra hne
        have hSubset : e ⊆ t := by
          rw [← hCarrier]
          exact heSub
        have heSmall : e.Subsingleton := by
          intro x hx y hy
          exact (hLinear heH htH hne)
            ⟨hx, hSubset hx⟩ ⟨hy, hSubset hy⟩
        exact hEdgeBig e heH heSmall
      have hft : f = t := by
        by_contra hne
        have hSubset : f ⊆ t := by
          rw [← hCarrier]
          exact hfSub
        have hfSmall : f.Subsingleton := by
          intro x hx y hy
          exact (hLinear hfH htH hne)
            ⟨hx, hSubset hx⟩ ⟨hy, hSubset hy⟩
        exact hEdgeBig f hfH hfSmall
      exact het.trans hft.symm
  change GirthGT (⋃ i : I, (T i).edges) g
  exact girthGT_union_of_forest T hTraceForest g
    (fun i => girthGT_of_edgeFamily_subsingleton (hEachSmall i) g)

/-- If each selected edge appears as the whole trace of some forest
member, then the selected support has girth exceeding any g. For the
manuscript one can choose the one-edge member e^+ as witness. -/
theorem girthGT_selected_of_forest_edge_traces
    [Fintype I]
    (F : I → HypergraphPiece W)
    (hForest : ForestOfCopies F)
    (S : Set W) (H : Set (Set W))
    (hLinear : LinearEdgeSet H)
    (hEdgeBig : ∀ e : Set W, e ∈ H → ¬ e.Subsingleton)
    (hTrace : ∀ i : I,
      ((F i).carrier ∩ S).Subsingleton ∨
        ∃ e : Set W, e ∈ H ∧ (F i).carrier ∩ S = e)
    (selected : Set (Set W))
    (hSelectedSub : selected ⊆ H)
    (hSelectedTrace : ∀ e : Set W, e ∈ selected →
      ∃ i : I, (F i).carrier ∩ S = e)
    (g : ℕ) :
    GirthGT selected g := by
  apply girthGT_of_subset ?_
    (girthGT_union_of_forest_edge_traces
      F hForest S H hLinear hEdgeBig hTrace g)
  intro e he
  obtain ⟨i, hi⟩ := hSelectedTrace e he
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  change e ∈ H ∧ e ⊆ (F i).carrier ∩ S
  exact ⟨hSelectedSub he, by rw [hi]; exact Set.Subset.rfl⟩

end StructuralRamsey.Girth

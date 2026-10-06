import Girth.Forest

/-! # Extending a running-intersection forest to a join tree

Several manuscript proofs first build an acyclic graph on the selected members
whose connected pieces already satisfy running intersection, and then connect
the components arbitrarily.  The arbitrary connections can be packaged by
extending the acyclic graph to a spanning tree.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- A finite acyclic graph which already has the running-intersection property
extends to a join tree.  The extension contains every old graph edge, so all
old occurrence-fibre connections are preserved. -/
theorem exists_joinTree_extension_of_acyclic_running
    {F : ι → HypergraphPiece W}
    [Finite ι] [Nonempty ι]
    (G : SimpleGraph ι)
    (hAcyclic : G.IsAcyclic)
    (hRunning :
      ∀ x : W,
        (G.induce {i : ι | x ∈ (F i).carrier}).Preconnected) :
    ∃ J : JoinTree F, G ≤ J.tree := by
  classical
  have hTop : (⊤ : SimpleGraph ι).Connected :=
    SimpleGraph.connected_top
  obtain ⟨T, hGT, _hTtop, hTree⟩ :=
    hTop.exists_isTree_le_of_le_of_isAcyclic
      (H := G) le_top hAcyclic
  refine ⟨{ tree := T, isTree := hTree, running := ?_ }, hGT⟩
  intro x
  have hInd :
      G.induce {i : ι | x ∈ (F i).carrier} ≤
        T.induce {i : ι | x ∈ (F i).carrier} := by
    intro a b hab
    exact hGT hab
  exact (hRunning x).mono hInd

end StructuralRamsey.Girth

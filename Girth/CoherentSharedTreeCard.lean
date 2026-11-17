import Girth.CoherentSharedOccurrence
import Girth.ForestTreeRewire

/-!
# From two local trees to the global tree certificate

This removes the CONNECTEDNESS assumption from coherent shared-index
gluing. If two embedded local trees cover the global index set and
share at least one index, the global graph is connected.

For finite global indices, combining that connectivity with the
edge-count equation |E| + 1 = |V| gives a tree. This is an honest
intermediate step toward the exact common-subtree quotient: the
edge-count equation is still a HYPOTHESIS here. A later theorem
must derive it from agreement of the two induced edge sets on
their shared connected subtree, not simply assume it.

No statement about A-copy closure or Ramsey witnesses follows.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {Q W : Type v}

/-- The vertex sets of two embedded local trees cover the global
index set and overlap nontrivially. Every global vertex can reach
one chosen shared index through one of the local trees. -/
theorem connected_of_embedded_local_trees
    (L R : Set Q)
    (hCover : L ∪ R = Set.univ)
    (hShared : (L ∩ R).Nonempty)
    (GL : SimpleGraph L) (GR : SimpleGraph R)
    (hGL : GL.IsTree) (hGR : GR.IsTree)
    (G : SimpleGraph Q)
    (hEdgesL : ∀ (i j : L), GL.Adj i j → G.Adj i.1 j.1)
    (hEdgesR : ∀ (i j : R), GR.Adj i j → G.Adj i.1 j.1) :
    G.Connected := by
  classical
  obtain ⟨k, hk⟩ := hShared
  let toGlobalL : GL →g G := {
    toFun := fun i => i.1
    map_rel' := by
      intro i j hij
      exact hEdgesL i j hij
  }
  let toGlobalR : GR →g G := {
    toFun := fun i => i.1
    map_rel' := by
      intro i j hij
      exact hEdgesR i j hij
  }
  have pathL (x : L) : G.Reachable x.1 k := by
    exact (hGL.connected x ⟨k, hk.1⟩).map toGlobalL
  have pathR (x : R) : G.Reachable x.1 k := by
    exact (hGR.connected x ⟨k, hk.2⟩).map toGlobalR
  letI : Nonempty Q := ⟨k⟩
  have pathToK (x : Q) : G.Reachable x k := by
    have hx : x ∈ L ∨ x ∈ R := by
      have h : x ∈ L ∪ R := by
        rw [hCover]
        exact Set.mem_univ x
      exact h
    rcases hx with hxL | hxR
    · exact pathL ⟨x, hxL⟩
    · exact pathR ⟨x, hxR⟩
  refine ⟨?_⟩
  intro x y
  exact (pathToK x).trans (pathToK y).symm

/-- A clean global join-tree certificate, with the edge-count
invariant exposed independently of running intersection.
The exact shared-subtree quotient should later *produce*
the global graph and this numerical certificate. -/
theorem joinTree_of_coherent_shared_indices_and_card
    [Finite Q]
    (F : Q → HypergraphPiece W)
    (L R : Set Q)
    (hCover : L ∪ R = Set.univ)
    (hSharedNonempty : (L ∩ R).Nonempty)
    (JL : JoinTree (fun i : L => F i.1))
    (JR : JoinTree (fun i : R => F i.1))
    (G : SimpleGraph Q)
    (hEdgesL : ∀ (i j : L), JL.tree.Adj i j → G.Adj i.1 j.1)
    (hEdgesR : ∀ (i j : R), JR.tree.Adj i j → G.Adj i.1 j.1)
    (hEdgeCount : G.edgeSet.ncard + 1 = Nat.card Q)
    (hOccurrences : SharedOccurrenceCoverage F L R) :
    JoinTree F := by
  have hConnected : G.Connected :=
    connected_of_embedded_local_trees L R hCover hSharedNonempty
      JL.tree JR.tree JL.isTree JR.isTree G hEdgesL hEdgesR
  exact joinTree_of_coherent_shared_indices F L R hCover JL JR G
    (isTree_of_connected_ncard_edgeSet G hConnected hEdgeCount)
    hEdgesL hEdgesR hOccurrences

/-- A generic typed-interface forest from the exact same
edge-count certificate and independently verified full overlaps. -/
theorem typedInterfaceForest_of_coherent_shared_indices_and_card
    [Finite Q]
    (F : Q → HypergraphPiece W)
    (compatible : HypergraphPiece W → HypergraphPiece W → Prop)
    (hCompatible : ∀ ⦃i j : Q⦄, i ≠ j → compatible (F i) (F j))
    (L R : Set Q) (hCover : L ∪ R = Set.univ)
    (hSharedNonempty : (L ∩ R).Nonempty)
    (JL : JoinTree (fun i : L => F i.1))
    (JR : JoinTree (fun i : R => F i.1))
    (G : SimpleGraph Q)
    (hEdgesL : ∀ (i j : L), JL.tree.Adj i j → G.Adj i.1 j.1)
    (hEdgesR : ∀ (i j : R), JR.tree.Adj i j → G.Adj i.1 j.1)
    (hEdgeCount : G.edgeSet.ncard + 1 = Nat.card Q)
    (hOccurrences : SharedOccurrenceCoverage F L R) :
    TypedInterfaceForest compatible F :=
  ⟨hCompatible,
    joinTree_of_coherent_shared_indices_and_card F L R
      hCover hSharedNonempty JL JR G
      hEdgesL hEdgesR hEdgeCount hOccurrences⟩

end CoherentPort
end StructuralRamsey.Girth

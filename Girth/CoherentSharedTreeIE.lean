import Girth.CoherentSharedTreeCard
import Mathlib.Data.Set.Card

/-!
# The shared-subtree edge-count criterion

If a finite graph is covered by two induced subtrees, and their
intersection is a tree, the exact edge inclusion–exclusion identity
makes the ambient graph a tree. The vertex inclusion–exclusion
identity is automatic from L ∪ R = univ.

The remaining combinatorial obligation is to show the edge identity
from exact agreement of local edge sets on a common subtree and
absence of edges crossing the private vertex sets. Here that
identity is stated EXPLICITLY; no circular IsTree assumption occurs.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {Q W : Type v}

/-- A finite graph is a tree if it is obtained from two overlapping
induced trees, the intersection is a tree, and its edge sets obey
the precise inclusion–exclusion identity. -/
theorem isTree_of_two_induced_trees_and_edge_IE
    [Finite Q]
    (G : SimpleGraph Q) (L R : Set Q)
    (hCover : L ∪ R = Set.univ)
    (hShared : (L ∩ R).Nonempty)
    (hTreeL : (G.induce L).IsTree)
    (hTreeR : (G.induce R).IsTree)
    (hTreeShared : (G.induce (L ∩ R)).IsTree)
    (hEdgeIE :
      G.edgeSet.ncard + (G.induce (L ∩ R)).edgeSet.ncard =
        (G.induce L).edgeSet.ncard + (G.induce R).edgeSet.ncard) :
    G.IsTree := by
  have hConn : G.Connected :=
    connected_of_embedded_local_trees L R hCover hShared
      (G.induce L) (G.induce R)
      hTreeL hTreeR G
      (by intro i j hij; exact hij)
      (by intro i j hij; exact hij)
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  have hVertexIE :
      Nat.card Q + (L ∩ R).ncard = L.ncard + R.ncard := by
    simpa [hCover, Set.ncard_univ] using
      (Set.ncard_union_add_ncard_inter L R)
  have hCounts (S : Set Q) (hS : (G.induce S).IsTree) :
      (G.induce S).edgeSet.ncard + 1 = S.ncard := by
    letI : Fintype S := Fintype.ofFinite S
    letI : Fintype (G.induce S).edgeSet := Fintype.ofFinite _
    have hEdges :
        Finset.card (G.induce S).edgeFinset =
          (G.induce S).edgeSet.ncard := by
      calc
        _ = Fintype.card (G.induce S).edgeSet :=
          (G.induce S).edgeFinset_card
        _ = (G.induce S).edgeSet.ncard :=
          Set.fintypeCard_eq_ncard _
    calc
      (G.induce S).edgeSet.ncard + 1 =
          Finset.card (G.induce S).edgeFinset + 1 :=
        congrArg (· + 1) hEdges.symm
      _ = Fintype.card S := hS.card_edgeFinset
      _ = S.ncard := Set.fintypeCard_eq_ncard S
  have hLeftCount := hCounts L hTreeL
  have hRightCount := hCounts R hTreeR
  have hSharedCount := hCounts (L ∩ R) hTreeShared
  have hTotalCount : G.edgeSet.ncard + 1 = Nat.card Q := by
    omega
  exact isTree_of_connected_ncard_edgeSet G hConn hTotalCount

/-- A fully typed incidence-forest version of the same card criterion.
The two tree structures on the same exact shared indices are the
underlying induced graphs of G; the extra physical vertex occurrence
condition provides global running intersection. -/
def typedInterfaceForest_of_induced_trees_and_edge_IE
    [Finite Q]
    (F : Q → HypergraphPiece W)
    (compatible : HypergraphPiece W → HypergraphPiece W → Prop)
    (hCompatible : ∀ ⦃i j : Q⦄, i ≠ j → compatible (F i) (F j))
    (G : SimpleGraph Q) (L R : Set Q)
    (hCover : L ∪ R = Set.univ)
    (hShared : (L ∩ R).Nonempty)
    (hTreeL : (G.induce L).IsTree)
    (hTreeR : (G.induce R).IsTree)
    (hTreeShared : (G.induce (L ∩ R)).IsTree)
    (hEdgeIE :
      G.edgeSet.ncard + (G.induce (L ∩ R)).edgeSet.ncard =
        (G.induce L).edgeSet.ncard + (G.induce R).edgeSet.ncard)
    (hOccL : ∀ (x : W),
      ((G.induce L).induce
        {i : L | x ∈ (F i.1).carrier}).Preconnected)
    (hOccR : ∀ (x : W),
      ((G.induce R).induce
        {i : R | x ∈ (F i.1).carrier}).Preconnected)
    (hSharedOcc : SharedOccurrenceCoverage F L R) :
    TypedInterfaceForest compatible F := by
  let JL : JoinTree (fun i : L => F i.1) :=
    ⟨G.induce L, hTreeL, hOccL⟩
  let JR : JoinTree (fun i : R => F i.1) :=
    ⟨G.induce R, hTreeR, hOccR⟩
  exact ⟨hCompatible,
    joinTree_of_coherent_shared_indices F L R hCover
      JL JR G
      (isTree_of_two_induced_trees_and_edge_IE
        G L R hCover hShared hTreeL hTreeR hTreeShared hEdgeIE)
      (by intro i j hij; exact hij)
      (by intro i j hij; exact hij)
      hSharedOcc⟩

end CoherentPort
end StructuralRamsey.Girth

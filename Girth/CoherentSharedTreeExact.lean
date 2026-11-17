import Girth.CoherentSharedTreeIE
import Mathlib.Data.Finset.Sym
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Exact common-subtree gluing: derive the edge count rather than assume it

For a finite graph G with vertex set covered by L and R, suppose:
  * G has no edge between L \ R and R \ L (free union);
  * G.induce L and G.induce R are trees;
  * G.induce (L ∩ R) is a tree.

Then G is a tree. The intersection is automatically the SAME
induced graph on both sides, so the forbidden differing shared
edge sets of the finite counterexample cannot occur.

We derive the edge inclusion–exclusion identity by identifying
each induced-edge finset with those ambient edges whose two
endpoints lie in the relevant subset. The earlier connectedness
lemma then supplies the rest.

This is the remaining graph-level component of coherent shared-
subtree gluing. Running intersection and typed intersections are
provided separately by CoherentSharedOccurrence and
CoherentSharedTreeIE. It makes no claim about Ramsey arrows or
newly created coloured A-copies.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {Q W : Type v}

/-- The ambient edges internal to a subset have the same cardinality
as the edge set of its induced graph. -/
theorem ncard_internal_edges_eq_induced
    [Finite Q] (G : SimpleGraph Q) (S : Set Q) :
    (G.edgeSet ∩ S.sym2).ncard = (G.induce S).edgeSet.ncard := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  letI : DecidableRel G.Adj := Classical.decRel _
  have hFinset :
      (G.edgeSet ∩ S.sym2).toFinset =
        G.edgeFinset ∩ S.toFinset.sym2 := by
    ext e
    induction e using Sym2.inductionOn
    simp [SimpleGraph.mem_edgeFinset,
      Finset.mk_mem_sym2_iff, Set.mk_mem_sym2_iff]
  have hMap := G.map_edgeFinset_induce (s := S)
  have hSourceCard :
      (G.induce S).edgeFinset.card =
        (G.induce S).edgeSet.ncard := by
    calc
      (G.induce S).edgeFinset.card =
          Fintype.card (G.induce S).edgeSet :=
        (G.induce S).edgeFinset_card
      _ = (G.induce S).edgeSet.ncard :=
        Set.fintypeCard_eq_ncard _
  calc
    (G.edgeSet ∩ S.sym2).ncard
      = (G.edgeSet ∩ S.sym2).toFinset.card :=
          Set.ncard_eq_toFinset_card _
    _ = (G.edgeFinset ∩ S.toFinset.sym2).card :=
          congrArg Finset.card hFinset
    _ = ((G.induce S).edgeFinset.map
          (Function.Embedding.subtype (· ∈ S)).sym2Map).card := by
            rw [hMap]
    _ = (G.induce S).edgeFinset.card := by
          simp only [Finset.card_map]
    _ = (G.induce S).edgeSet.ncard := hSourceCard

/-- If every ambient edge lies wholly inside at least one side,
the ambient edge set is the union of its two internal edge sets.
The absence of cross-private edges supplies this condition. -/
theorem edgeSet_internal_union_of_free_cover
    (G : SimpleGraph Q) (L R : Set Q)
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃x y : Q⦄, x ∈ L \ R → y ∈ R \ L → ¬ G.Adj x y) :
    (G.edgeSet ∩ L.sym2) ∪ (G.edgeSet ∩ R.sym2) = G.edgeSet := by
  classical
  ext e
  induction e using Sym2.inductionOn
  rename_i x y
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mk_mem_sym2_iff]
  constructor
  · rintro (⟨hG, _⟩ | ⟨hG, _⟩) <;> exact hG
  · intro hG
    have hx : x ∈ L ∨ x ∈ R := by
      have h : x ∈ L ∪ R := by
        rw [hCover]
        exact Set.mem_univ _
      exact h
    have hy : y ∈ L ∨ y ∈ R := by
      have h : y ∈ L ∪ R := by
        rw [hCover]
        exact Set.mem_univ _
      exact h
    by_cases hLL : x ∈ L ∧ y ∈ L
    · exact Or.inl ⟨hG, hLL⟩
    by_cases hRR : x ∈ R ∧ y ∈ R
    · exact Or.inr ⟨hG, hRR⟩
    have hBad :
        (x ∈ L \ R ∧ y ∈ R \ L) ∨
        (y ∈ L \ R ∧ x ∈ R \ L) := by
      simp only [Set.mem_diff]
      tauto
    rcases hBad with ⟨hxL, hyR⟩ | ⟨hyL, hxR⟩
    · exact (hNoCross hxL hyR hG).elim
    · exact (hNoCross hyL hxR (G.symm hG)).elim

/-- Edge inclusion–exclusion for an actual free union. Exact shared
indexing is essential: the intersection of internal edge sets is
precisely the edge set internal to L ∩ R. -/
theorem edgeSet_induced_inclusion_exclusion
    [Finite Q]
    (G : SimpleGraph Q) (L R : Set Q)
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃x y : Q⦄, x ∈ L \ R → y ∈ R \ L → ¬ G.Adj x y) :
    G.edgeSet.ncard + (G.induce (L ∩ R)).edgeSet.ncard =
      (G.induce L).edgeSet.ncard + (G.induce R).edgeSet.ncard := by
  classical
  let EL : Set (Sym2 Q) := G.edgeSet ∩ L.sym2
  let ER : Set (Sym2 Q) := G.edgeSet ∩ R.sym2
  have hUnion : EL ∪ ER = G.edgeSet :=
    edgeSet_internal_union_of_free_cover G L R hCover hNoCross
  have hInter :
      EL ∩ ER = G.edgeSet ∩ (L ∩ R).sym2 := by
    ext e
    change (e ∈ G.edgeSet ∩ L.sym2 ∧ e ∈ G.edgeSet ∩ R.sym2) ↔
      e ∈ G.edgeSet ∩ (L ∩ R).sym2
    rw [Set.sym2_inter]
    simp only [Set.mem_inter_iff]
    tauto
  have hIE := Set.ncard_union_add_ncard_inter EL ER
  rw [hUnion, hInter] at hIE
  have hEL : EL.ncard = (G.induce L).edgeSet.ncard :=
    ncard_internal_edges_eq_induced G L
  have hER : ER.ncard = (G.induce R).edgeSet.ncard :=
    ncard_internal_edges_eq_induced G R
  have hEK :
      (G.edgeSet ∩ (L ∩ R).sym2).ncard =
        (G.induce (L ∩ R)).edgeSet.ncard :=
    ncard_internal_edges_eq_induced G (L ∩ R)
  simpa only [hEL, hER, hEK] using hIE

/-- Full graph-theoretic shared-subtree gluing, with no tree,
connectivity or numerical cardinality assumption on the output. -/
theorem isTree_of_two_induced_trees_free_union
    [Finite Q]
    (G : SimpleGraph Q) (L R : Set Q)
    (hCover : L ∪ R = Set.univ)
    (hShared : (L ∩ R).Nonempty)
    (hTreeL : (G.induce L).IsTree)
    (hTreeR : (G.induce R).IsTree)
    (hTreeShared : (G.induce (L ∩ R)).IsTree)
    (hNoCross : ∀ ⦃x y : Q⦄, x ∈ L \ R → y ∈ R \ L → ¬ G.Adj x y) :
    G.IsTree :=
  isTree_of_two_induced_trees_and_edge_IE
    G L R hCover hShared hTreeL hTreeR hTreeShared
    (edgeSet_induced_inclusion_exclusion G L R hCover hNoCross)

/-- Full coherent join-tree amalgamation with a parameterized policy
of allowed full intersections. Remaining new-A-copy and closure
conditions are not consequences of the join-tree conclusion. -/
def typedInterfaceForest_of_free_shared_subtree
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
    (hNoCross : ∀ ⦃x y : Q⦄, x ∈ L \ R → y ∈ R \ L → ¬ G.Adj x y)
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
      (isTree_of_two_induced_trees_free_union
        G L R hCover hShared hTreeL hTreeR hTreeShared hNoCross)
      (by intro i j hij; exact hij)
      (by intro i j hij; exact hij)
      hSharedOcc⟩

end CoherentPort
end StructuralRamsey.Girth

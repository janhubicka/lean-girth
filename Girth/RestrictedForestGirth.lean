import Girth.CarrierForestGirth

/-! # Restricting a forest to one vertex part

The manuscript later restricts every member of a forest to one part of a
partite system.  If every common support edge meets that part in at most one
vertex, all restricted carrier intersections are subsingleton.  The abstract
carrier-forest girth theorem then excludes every Berge cycle.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Restrict only the carrier of a piece to a prescribed vertex set.  The edge
field is irrelevant for the resulting carrier hypergraph and is left empty. -/
def HypergraphPiece.restrictCarrier
    (F : HypergraphPiece W) (P : Set W) : HypergraphPiece W where
  carrier := F.carrier ∩ P
  edges := ∅
  edge_subset_carrier := by
    intro e he
    simp at he

/-- The same join tree works after restricting every carrier to a fixed vertex
set. -/
def JoinTree.restrictCarriers
    {F : ι → HypergraphPiece W}
    (J : JoinTree F) (P : Set W) :
    JoinTree (fun i => (F i).restrictCarrier P) where
  tree := J.tree
  isTree := J.isTree
  running := by
    intro x
    by_cases hx : x ∈ P
    · have hOcc :
          {i : ι | x ∈ ((F i).restrictCarrier P).carrier} =
            {i : ι | x ∈ (F i).carrier} := by
        ext i
        simp [HypergraphPiece.restrictCarrier, hx]
      rw [hOcc]
      exact J.running x
    · intro a b
      have haProp := a.property
      change x ∈ (F a.1).carrier ∩ P at haProp
      exact (hx haProp.2).elim

/-- Allowed full intersections become subsingleton after restriction whenever
every common support edge meets the restricting set in at most one vertex. -/
theorem pairwise_restrictedCarrier_subsingleton_of_allowed
    {F : ι → HypergraphPiece W}
    (hAllowed : PairwiseAllowed F)
    (P : Set W)
    (hEdgePart :
      ∀ ⦃i j : ι⦄, i ≠ j → ∀ ⦃e : Set W⦄,
        e ∈ (F i).edges → e ∈ (F j).edges →
          (e ∩ P).Subsingleton) :
    ∀ ⦃i j : ι⦄, i ≠ j →
      (((F i).restrictCarrier P).carrier ∩
        ((F j).restrictCarrier P).carrier).Subsingleton := by
  intro i j hij
  rcases hAllowed hij with hSmall | hEdge
  · intro x hx y hy
    apply hSmall
    · exact ⟨hx.1.1, hx.2.1⟩
    · exact ⟨hy.1.1, hy.2.1⟩
  · rcases hEdge with ⟨e, hei, hej, hInter⟩
    have hEP : (e ∩ P).Subsingleton :=
      hEdgePart hij hei hej
    intro x hx y hy
    apply hEP
    · constructor
      · have hxBoth : x ∈ (F i).carrier ∩ (F j).carrier :=
          ⟨hx.1.1, hx.2.1⟩
        rw [hInter] at hxBoth
        exact hxBoth
      · exact hx.1.2
    · constructor
      · have hyBoth : y ∈ (F i).carrier ∩ (F j).carrier :=
          ⟨hy.1.1, hy.2.1⟩
        rw [hInter] at hyBoth
        exact hyBoth
      · exact hy.1.2

/-- Restricting a finite forest to such a part gives a carrier hypergraph of
girth above every prescribed finite bound. -/
theorem girthGT_restrictedCarrierEdgeFamily_of_forest
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι]
    (hForest : ForestOfCopies F)
    (P : Set W)
    (hEdgePart :
      ∀ ⦃i j : ι⦄, i ≠ j → ∀ ⦃e : Set W⦄,
        e ∈ (F i).edges → e ∈ (F j).edges →
          (e ∩ P).Subsingleton)
    (g : ℕ) :
    GirthGT
      (carrierEdgeFamily
        (fun i => (F i).restrictCarrier P)) g := by
  obtain ⟨J⟩ := hForest.joinTree_of_nonempty
  exact girthGT_carrierEdgeFamily_of_joinTree
    (J.restrictCarriers P)
    (pairwise_restrictedCarrier_subsingleton_of_allowed
      hForest.pairwiseAllowed P hEdgePart)
    g

/-- A vertex set behaves like one part of a partite support system when every
support edge of every member meets it in at most one vertex. -/
def EdgesMeetPartAtMostOne
    (F : ι → HypergraphPiece W) (P : Set W) : Prop :=
  ∀ i : ι, ∀ ⦃e : Set W⦄,
    e ∈ (F i).edges → (e ∩ P).Subsingleton

/-- Manuscript form of the one-part observation: a finite forest restricted to
a vertex part met at most once by every support edge has no Berge cycle of any
prescribed bounded length. -/
theorem girthGT_restrictedCarrierEdgeFamily_of_part
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι]
    (hForest : ForestOfCopies F)
    (P : Set W)
    (hPart : EdgesMeetPartAtMostOne F P)
    (g : ℕ) :
    GirthGT
      (carrierEdgeFamily
        (fun i => (F i).restrictCarrier P)) g := by
  exact girthGT_restrictedCarrierEdgeFamily_of_forest
    hForest P
    (by
      intro i j hij e hei hej
      exact hPart i hei)
    g

end StructuralRamsey.Girth

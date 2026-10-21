import Girth.ForestAttach

/-!
# Attaching arbitrary subsingleton-carrier pieces to a forest

The strengthened covered-family lemma uses the actual singleton separator
as an auxiliary instead of selecting an incident ambient support edge.
This construction works even for isolated vertices. No new support edges
are introduced and no girth condition is required for this attachment.

The proof uses the verified finite dominated-attachment theorem: all
intersections of a subsingleton carrier with old pieces are comparable,
so one old piece dominates them.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- Any auxiliary member with empty or singleton carrier may be added as
a leaf to a nonempty forest.  Repeated singleton labels are permitted.
The result remains a forest of labelled pieces, not just an unlabelled set. -/
theorem ForestOfCopies.append_subsingletonCarrier
    [Fintype I] [Nonempty I]
    {F : I → HypergraphPiece W}
    (hF : ForestOfCopies F)
    (S : HypergraphPiece W)
    (hSmall : S.carrier.Subsingleton) :
    ForestOfCopies (sumPieces F (fun _ : PUnit.{v+1} => S)) := by
  classical
  have hCross : ∀ i : I, AllowedIntersection (F i) S := by
    intro i
    left
    intro x hx y hy
    exact hSmall hx.2 hy.2
  have hComparable :
      ∀ i j : I,
        S.carrier ∩ (F i).carrier ⊆
          S.carrier ∩ (F j).carrier ∨
        S.carrier ∩ (F j).carrier ⊆
          S.carrier ∩ (F i).carrier := by
    intro i j
    by_cases hij :
        S.carrier ∩ (F i).carrier ⊆
          S.carrier ∩ (F j).carrier
    · exact Or.inl hij
    · right
      obtain ⟨x, hx, _hn⟩ := Set.not_subset.mp hij
      intro y hy
      have hyx : y = x := hSmall hy.1 hx.1
      simpa [hyx] using hx
  obtain ⟨p, hp⟩ :=
    exists_dominating_member_of_comparable S hComparable
  exact forestOfCopies_attach_dominated hF S hCross p hp

end StructuralRamsey.Girth

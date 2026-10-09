import Girth.ForestMarkedLeafAttachment

/-!
# Two marked witnesses for a failed forest leaf attachment

The circulation proof permits an old forest indexed by finitely many
members, even when its ambient vertex type is infinite. If pairwise
old/new intersections are allowed but the result is not a forest,
there are two incomparable old contacts.

When all old/new contacts lie on the fixed finite marked boundary,
the two incomparable contacts can be represented by two ACTUAL old
carriers from the bounded finite family of marked-mask witnesses.
Thus a bad one-piece extension has a two-carrier *geometric*
certificate. This is a necessary obstruction, not by itself a
two-presentation successor-tree Ramsey test.
-/

namespace StructuralRamsey.Girth

universe u v
variable {I : Type u} [Fintype I]
variable {W ι : Type v}

/-- A failed one-piece forest attachment with allowed pairwise
intersections has two incomparable old contacts, and their physical
contact geometry survives replacing the old carriers by finite
marked-mask representatives. No finiteness of W is assumed. -/
theorem badForest_two_incomparable_marked_contacts
    [Fintype ι] [Nonempty ι]
    {Y : ι → HypergraphPiece W}
    (hY : ForestOfCopies Y)
    (F : HypergraphPiece W)
    (f : I → W) (S : Set I)
    (hContact :
      ∀ D ∈ Set.range (fun i : ι => (Y i).carrier),
        F.carrier ∩ D = (f '' S) ∩ D)
    (hCrossAllowed :
      ∀ i : ι, AllowedIntersection (Y i) F)
    (hBad :
      ¬ ForestOfCopies
        (sumPieces Y (fun _ : PUnit.{v+1} => F))) :
    ∃ R ∈ markedCarrierRepresentatives
        (Set.range (fun i : ι => (Y i).carrier)) f,
      ∃ T ∈ markedCarrierRepresentatives
          (Set.range (fun i : ι => (Y i).carrier)) f,
        ¬(F.carrier ∩ R ⊆ F.carrier ∩ T) ∧
        ¬(F.carrier ∩ T ⊆ F.carrier ∩ R) := by
  classical
  obtain ⟨i, j, hij, hji⟩ :=
    exists_incomparable_intersections_of_not_forest
      hY F hCrossAllowed hBad
  let family : Set (Set W) :=
    Set.range (fun i : ι => (Y i).carrier)
  obtain ⟨R, hR, hMaskR⟩ :=
    markedCarrierRepresentatives_cover
      family f (Y i).carrier ⟨i, rfl⟩
  obtain ⟨T, hT, hMaskT⟩ :=
    markedCarrierRepresentatives_cover
      family f (Y j).carrier ⟨j, rfl⟩
  have hRFamily : R ∈ family :=
    markedCarrierRepresentatives_subset family f R hR
  have hTFamily : T ∈ family :=
    markedCarrierRepresentatives_subset family f T hT
  have hEqualR : F.carrier ∩ (Y i).carrier = F.carrier ∩ R :=
    freshCarrier_inter_eq_of_sameMask
      family f S F.carrier (Y i).carrier R
      hContact ⟨i, rfl⟩ hRFamily hMaskR.symm
  have hEqualT : F.carrier ∩ (Y j).carrier = F.carrier ∩ T :=
    freshCarrier_inter_eq_of_sameMask
      family f S F.carrier (Y j).carrier T
      hContact ⟨j, rfl⟩ hTFamily hMaskT.symm
  rw [hEqualR, hEqualT] at hij hji
  exact ⟨R, hR, T, hT, hij, hji⟩

/-- Conversely, if all contacts between the fresh carrier and the
bounded marked-carrier representative family are comparable by
inclusion, the fresh piece can be attached as a dominated leaf.
This is stronger than pairwise allowedness alone. -/
theorem forestOfCopies_attach_of_comparable_marked_contacts
    [Fintype ι] [Nonempty ι]
    {Y : ι → HypergraphPiece W}
    (hY : ForestOfCopies Y)
    (F : HypergraphPiece W)
    (f : I → W) (S : Set I)
    (hContact :
      ∀ D ∈ Set.range (fun i : ι => (Y i).carrier),
        F.carrier ∩ D = (f '' S) ∩ D)
    (hCrossAllowed :
      ∀ i : ι, AllowedIntersection (Y i) F)
    (hComparable :
      ∀ R ∈ markedCarrierRepresentatives
          (Set.range (fun i : ι => (Y i).carrier)) f,
        ∀ T ∈ markedCarrierRepresentatives
            (Set.range (fun i : ι => (Y i).carrier)) f,
          F.carrier ∩ R ⊆ F.carrier ∩ T ∨
            F.carrier ∩ T ⊆ F.carrier ∩ R) :
    ForestOfCopies
      (sumPieces Y (fun _ : PUnit.{v+1} => F)) := by
  by_contra hBad
  obtain ⟨R, hR, T, hT, hRT, hTR⟩ :=
    badForest_two_incomparable_marked_contacts
      hY F f S hContact hCrossAllowed hBad
  rcases hComparable R hR T hT with hIncl | hIncl
  · exact hRT hIncl
  · exact hTR hIncl

end StructuralRamsey.Girth

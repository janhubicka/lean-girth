import Girth.ForestMarkedCarrierContacts
import Girth.ForestAttach
import Mathlib.Tactic

/-!
# Finite boundary certificate for one dominated forest attachment

The finite marked-carrier masks already preserve all *individual* old/new
intersections when the new carrier meets old material only at marked
boundary vertices.  Here this observation is used with the existing
dominated-leaf construction of an actual join tree.

An old carrier dominates all contacts with a proposed fresh carrier if and
only if a chosen representative of one of finitely many marked intersection
masks dominates all the other representatives.  When the original old
family is a forest and all cross intersections are allowed, such a
representative certifies that adjoining the fresh carrier as a leaf
preserves the forest condition.

The theorem concerns dominated leaf attachments.  A new carrier may also
attach to several distinct old components by a more general join tree.
Nor does this construct the free-ancestral history of an attachment.
-/

namespace StructuralRamsey.Girth

universe u v
variable {I : Type u} {W : Type v} [Fintype I]

/-- Existence of a single old carrier dominating every old/new
intersection is exactly captured by the finite set of old
marked-mask representatives.  This includes arbitrary, possibly
infinite, families of old carriers. -/
theorem freshCarrier_dominated_iff_representatives
    (family : Set (Set W)) (f : I → W) (S : Set I)
    (e : Set W)
    (hContact : ∀ D ∈ family, e ∩ D = (f '' S) ∩ D) :
    (∃ P ∈ family, ∀ D ∈ family, e ∩ D ⊆ e ∩ P) ↔
    (∃ P ∈ markedCarrierRepresentatives family f,
      ∀ R ∈ markedCarrierRepresentatives family f,
        e ∩ R ⊆ e ∩ P) := by
  classical
  constructor
  · rintro ⟨P, hP, hDominates⟩
    obtain ⟨R, hR, hMask⟩ :=
      markedCarrierRepresentatives_cover family f P hP
    have hRFamily : R ∈ family :=
      markedCarrierRepresentatives_subset family f R hR
    have hEq : e ∩ P = e ∩ R :=
      freshCarrier_inter_eq_of_sameMask
        family f S e P R hContact hP hRFamily hMask.symm
    refine ⟨R, hR, ?_⟩
    intro Q hQ
    have hQFamily : Q ∈ family :=
      markedCarrierRepresentatives_subset family f Q hQ
    exact (hDominates Q hQFamily).trans hEq.subset
  · rintro ⟨P, hP, hDominates⟩
    have hPFamily : P ∈ family :=
      markedCarrierRepresentatives_subset family f P hP
    refine ⟨P, hPFamily, ?_⟩
    intro D hD
    obtain ⟨R, hR, hMask⟩ :=
      markedCarrierRepresentatives_cover family f D hD
    have hRFamily : R ∈ family :=
      markedCarrierRepresentatives_subset family f R hR
    have hEq : e ∩ D = e ∩ R :=
      freshCarrier_inter_eq_of_sameMask
        family f S e D R hContact hD hRFamily hMask.symm
    rw [hEq]
    exact hDominates R hR

/-- The circulation forest's dominated-leaf step can be certified by
checking the bounded set of marked B-carrier representatives rather than
all members of the old family.  The forest itself, including its join
tree, is not replaced by the representative subfamily. -/
theorem forestOfCopies_attach_dominated_of_marked_contacts
    {ι : Type v} [Fintype ι] [Nonempty ι]
    {Y : ι → HypergraphPiece W}
    (hY : ForestOfCopies Y)
    (F : HypergraphPiece W)
    (f : I → W) (S : Set I)
    (hContact :
      ∀ D ∈ Set.range (fun i : ι => (Y i).carrier),
        F.carrier ∩ D = (f '' S) ∩ D)
    (hCrossAllowed : ∀ i : ι, AllowedIntersection (Y i) F)
    (hRepresentativeDominates :
      ∃ P ∈ markedCarrierRepresentatives
          (Set.range (fun i : ι => (Y i).carrier)) f,
        ∀ R ∈ markedCarrierRepresentatives
            (Set.range (fun i : ι => (Y i).carrier)) f,
          F.carrier ∩ R ⊆ F.carrier ∩ P) :
    ForestOfCopies (sumPieces Y (fun _ : PUnit.{v+1} => F)) := by
  classical
  have hExists :
      ∃ P ∈ Set.range (fun i : ι => (Y i).carrier),
        ∀ D ∈ Set.range (fun i : ι => (Y i).carrier),
          F.carrier ∩ D ⊆ F.carrier ∩ P :=
    (freshCarrier_dominated_iff_representatives
      (Set.range (fun i : ι => (Y i).carrier))
      f S F.carrier hContact).mpr hRepresentativeDominates
  obtain ⟨P, ⟨p, rfl⟩, hDominates⟩ := hExists
  apply forestOfCopies_attach_dominated hY F hCrossAllowed p
  intro i
  exact hDominates (Y i).carrier ⟨i, rfl⟩

/-- Failure of an allowed one-leaf attachment to form a forest rules out
the existence of a dominating representative.  This is an implication,
not a characterization of *all* bad attachment patterns. -/
theorem no_marked_dominating_representative_of_bad_attachment
    {ι : Type v} [Fintype ι] [Nonempty ι]
    {Y : ι → HypergraphPiece W}
    (hY : ForestOfCopies Y)
    (F : HypergraphPiece W)
    (f : I → W) (S : Set I)
    (hContact :
      ∀ D ∈ Set.range (fun i : ι => (Y i).carrier),
        F.carrier ∩ D = (f '' S) ∩ D)
    (hCrossAllowed : ∀ i : ι, AllowedIntersection (Y i) F)
    (hBad :
      ¬ ForestOfCopies (sumPieces Y (fun _ : PUnit.{v+1} => F))) :
    ¬ ∃ P ∈ markedCarrierRepresentatives
        (Set.range (fun i : ι => (Y i).carrier)) f,
      ∀ R ∈ markedCarrierRepresentatives
          (Set.range (fun i : ι => (Y i).carrier)) f,
        F.carrier ∩ R ⊆ F.carrier ∩ P := by
  intro hDominates
  exact hBad
    (forestOfCopies_attach_dominated_of_marked_contacts
      hY F f S hContact hCrossAllowed hDominates)

end StructuralRamsey.Girth

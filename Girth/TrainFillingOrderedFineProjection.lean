import Girth.TrainFillingOrderedCanonicalPlacement
import Girth.TrainFillingColouredOrderedEdgePresentation

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

variable {I : Type u} {X Y : Type v} {k : ℕ}
variable (N : RelStructure (colouredOrderedEdgeLanguage I k).withOrder Y)
variable (enumerate : X ≃ ULift.{v} (Fin k)) (part : X → I)

private abbrev orderedFineSource :=
  (colouredOrderedEdgeSource k (fun i => part (enumerate.symm (ULift.up i)))).ordered

local notation "OldEdge" =>
  {s : Set Y // s ∈ supportCopies (orderedFineSource enumerate part) N}

/-- The shortened language remembers the original template's part as a
unary predicate. A vertex can have different template coordinates in
different old edges, but every occurrence specifies the same part. -/
def shortenedHasPart (y : Y) (i : I) : Prop :=
  N.rel (.inl (.inl (.inr i))) (fun _ => y)

theorem orderedFillingPlacement_hasPart_iff (e : OldEdge) (x : X) (i : I) :
    shortenedHasPart N (orderedFillingPlacement enumerate e x) i ↔ part x = i := by
  let a : Embedding (orderedFineSource enumerate part) N := Classical.choose e.2
  have h := a.map_rel_iff (.inl (.inl (.inr i))) (fun _ => enumerate x)
  change shortenedHasPart N (orderedFillingPlacement enumerate e x) i ↔
    part (enumerate.symm (enumerate x)) = i at h
  simpa only [Equiv.symm_apply_apply] using h

/-- Full old-edge coverage forces every witness vertex to carry exactly
one original part predicate. -/
theorem shortenedHasPart_existsUnique
    (hOldCover : ∀ y : Y, ∃ e : OldEdge, y ∈ e.1)
    (y : Y) : ∃! i, shortenedHasPart N y i := by
  obtain ⟨e, he⟩ := hOldCover y
  rw [← orderedFillingPlacement_range enumerate e] at he
  obtain ⟨x, rfl⟩ := he
  refine ⟨part x, (orderedFillingPlacement_hasPart_iff N enumerate part e x _).mpr rfl, ?_⟩
  intro i hi
  exact ((orderedFillingPlacement_hasPart_iff N enumerate part e x i).mp hi).symm

/-- The fine projection of the entire filled vertex set is determined by
the actual unary predicates of the shortened witness. -/
noncomputable def orderedFillingPart
    (hOldCover : ∀ y : Y, ∃ e : OldEdge, y ∈ e.1) (y : Y) : I :=
  Classical.choose (shortenedHasPart_existsUnique N enumerate part hOldCover y)

theorem shortenedHasPart_iff_part_eq
    (hOldCover : ∀ y : Y, ∃ e : OldEdge, y ∈ e.1) (y : Y) (i : I) :
    shortenedHasPart N y i ↔ orderedFillingPart N enumerate part hOldCover y = i := by
  have hPart := Classical.choose_spec (shortenedHasPart_existsUnique N enumerate part hOldCover y)
  constructor
  · intro hi
    exact (hPart.2 i hi).symm
  · intro hi
    rw [← hi]
    exact hPart.1

theorem orderedFillingPart_place
    (hOldCover : ∀ y : Y, ∃ e : OldEdge, y ∈ e.1) (e : OldEdge) (x : X) :
    orderedFillingPart N enumerate part hOldCover (orderedFillingPlacement enumerate e x) =
      part x := by
  exact (shortenedHasPart_iff_part_eq N enumerate part hOldCover _ _).mp
    ((orderedFillingPlacement_hasPart_iff N enumerate part e x _).mpr rfl)

end StructuralRamsey.Girth

import PartiteConstruction.Partite.InducedStep

/-! # Custom local witnesses in an induced picture step

The generic induced construction in `partite-construction` chooses the
coordinate-power Partite-Lemma witness internally.  The girth manuscript needs
the same free-attachment shell with a stronger local witness supplied by the
local-forest lemma.  This module exposes precisely that reusable shell.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P X Y : Type v}

/-- One induced picture step with an arbitrary local Ramsey witness.

The local system `E` replaces the positive coordinate power used by the
generic Picture Lemma.  Once `E` is A-partite and has the required partite
Ramsey arrow, the existing free attachment preserves both the
homomorphism-embedding projection invariant and irreducible coverage. -/
theorem customInducedPictureStep
    (A : RelStructure L U)
    (B₀ : RelStructure L V)
    (D₀ : RelStructure L P)
    (C₀ : StructuralRamsey.Partite.System L P X)
    (α : StructuralRamsey.Partite.Induced.RelevantEmbedding A B₀ D₀)
    (E : StructuralRamsey.Partite.System L U Y)
    (κ : Type*)
    (hPartite : C₀.IsPartiteOver D₀)
    (hCover :
      StructuralRamsey.Partite.CoversIrreduciblesBy C₀ B₀ D₀)
    (hE : E.IsPartiteOver A)
    (hArrow :
      StructuralRamsey.Partite.Arrow
        (StructuralRamsey.Partite.transversal A)
        (C₀.restrict α.1.toFunctionEmbedding) E κ) :
    let αf := α.1.toFunctionEmbedding
    let C₁ := StructuralRamsey.Partite.Picture.build C₀ αf E
    C₁.IsPartiteOver D₀ ∧
      StructuralRamsey.Partite.CoversIrreduciblesBy C₁ B₀ D₀ ∧
      StructuralRamsey.Partite.PictureProperty A C₀ αf C₁ κ := by
  classical
  let αf := α.1.toFunctionEmbedding
  let C₁ := StructuralRamsey.Partite.Picture.build C₀ αf E
  have hCorePartite :
      (E.relabel αf).IsPartiteOver D₀ :=
    StructuralRamsey.Partite.Induced.relabel_isPartiteOver
      (A := A) (B := E) hE α.1
  have hC₁Partite : C₁.IsPartiteOver D₀ := by
    exact StructuralRamsey.Partite.Attachment.attach_isPartiteOver
      C₀ (C₀.support αf) (E.relabel αf)
      (StructuralRamsey.Partite.Picture.attachingMap C₀ αf E)
      hPartite hCorePartite
  have hCoreCover :
      StructuralRamsey.Partite.CoversIrreduciblesBy
        (E.relabel αf) B₀ D₀ :=
    StructuralRamsey.Partite.Induced.relabel_covers_of_relevant
      A B₀ D₀ E α
  have hC₁Cover :
      StructuralRamsey.Partite.CoversIrreduciblesBy C₁ B₀ D₀ := by
    exact StructuralRamsey.Partite.Induced.Attachment.attach_covers
      B₀ D₀ C₀ (C₀.support αf) (E.relabel αf)
      (StructuralRamsey.Partite.Picture.attachingMap C₀ αf E)
      hCover hCoreCover
  have hPicture :
      StructuralRamsey.Partite.PictureProperty A C₀ αf C₁ κ :=
    StructuralRamsey.Partite.Picture.property C₀ αf E κ hArrow
  exact ⟨hC₁Partite, hC₁Cover, hPicture⟩

end StructuralRamsey.Girth

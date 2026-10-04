import Girth.ActivePicture
import PartiteConstruction.Iterated.FinalAttachment

/-! # Actual B-copy coverage through a simultaneous picture attachment

The induced partite construction tracks a projection-only irreducible invariant.
The local-tree proof needs the stronger relational statement that every
irreducible substructure is contained in an actual copy of the designated
base structure.  The free-attachment core-or-copy dichotomy preserves this
stronger invariant as soon as it holds on both sides.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {VB P X Y I : Type v}

/-- Actual-copy irreducible coverage is preserved by a simultaneous partite
attachment when it holds both in the old picture and in the local core. -/
theorem irreduciblesExtendTo_partiteAttachment
    (B₀ : RelStructure L VB)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (hC : RelStructure.IrreduciblesExtendTo B₀ C.toRelStructure)
    (hE : RelStructure.IrreduciblesExtendTo B₀ E.toRelStructure) :
    RelStructure.IrreduciblesExtendTo B₀
      (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure := by
  classical
  let Whole :=
    (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure
  intro T hT
  let inc : RelStructure.Embedding (Whole.induce T) Whole :=
    RelStructure.inclusion Whole T
  have hsplit :=
    RelStructure.Attachment.irreducible_core_or_copy
      (B := C.toRelStructure) (S := S) (D := E.toRelStructure)
      (f := fun i => (f i).toEmbedding) T hT
  rcases hsplit with hcore | ⟨i, hcopy⟩
  · let core : RelStructure.Embedding E.toRelStructure Whole :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    have hrange :
        ∀ z : T, ∃ y : Y, inc z = core y := by
      intro z
      rcases hcore z with ⟨y, hy⟩
      exact ⟨y, hy⟩
    let eE : RelStructure.Embedding (Whole.induce T) E.toRelStructure :=
      inc.factorThroughRange core hrange
    let Rng : Set Y := Set.range eE
    have hRng : (E.toRelStructure.induce Rng).Irreducible :=
      hT.range_embedding eE
    obtain ⟨β, hβ⟩ := hE Rng hRng
    refine ⟨core.comp β, ?_⟩
    intro z
    let q : Rng := ⟨eE z, ⟨z, rfl⟩⟩
    obtain ⟨b, hb⟩ := hβ q
    refine ⟨b, ?_⟩
    have hz := Classical.choose_spec (hrange z)
    change z.1 = core (β b)
    calc
      z.1 = inc z := rfl
      _ = core (eE z) := hz
      _ = core (β b) := congrArg core hb
  · let copy : RelStructure.Embedding C.toRelStructure Whole :=
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
    have hrange :
        ∀ z : T, ∃ x : X, inc z = copy x := by
      intro z
      rcases hcopy z with ⟨x, hx⟩
      exact ⟨x, hx⟩
    let eC : RelStructure.Embedding (Whole.induce T) C.toRelStructure :=
      inc.factorThroughRange copy hrange
    let Rng : Set X := Set.range eC
    have hRng : (C.toRelStructure.induce Rng).Irreducible :=
      hT.range_embedding eC
    obtain ⟨β, hβ⟩ := hC Rng hRng
    refine ⟨copy.comp β, ?_⟩
    intro z
    let q : Rng := ⟨eC z, ⟨z, rfl⟩⟩
    obtain ⟨b, hb⟩ := hβ q
    refine ⟨b, ?_⟩
    have hz := Classical.choose_spec (hrange z)
    change z.1 = copy (β b)
    calc
      z.1 = inc z := rfl
      _ = copy (eC z) := hz
      _ = copy (β b) := congrArg copy hb

end StructuralRamsey.Girth

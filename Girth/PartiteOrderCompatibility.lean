import Girth.ActivePicture
import PartiteConstruction.Relational.Order

/-!
# Compatibility of a partite picture with the auxiliary base order

The circulation proof maintains that an occurrence of the distinguished
binary order symbol in the picture projects forward along the fixed
auxiliary linear order of the Ramsey base. This is preserved under
the standard free picture attachment because every relation tuple
comes entirely from its local core or one old standard picture.

The result is independent of the local Ramsey arrow and foresthood.
The separate local-witness obligation is to prove compatibility of
the new core, using its A-generation and the agreement of the base
order with the original order on the processed A-copy.
-/

namespace StructuralRamsey.Girth

universe u v
variable {L : RelLanguage.{u}}
variable {P X Y I : Type v}

/-- The order relation of a partite system moves strictly forward in
a chosen auxiliary base order. This is the manuscript's (ordercompat)
invariant; it does not require the picture's own order to be total. -/
def PartiteOrderCompatible
    [LT P]
    (C : StructuralRamsey.Partite.System L.withOrder P X) : Prop :=
  ∀ x y : X,
    C.toRelStructure.rel (.inr ()) ![x, y] → C.part x < C.part y

/-- Free attachment preserves order compatibility exactly, assuming it
for the old standard picture and the new local core. No total order or
transitivity on the picture vertices is imposed. -/
theorem partiteOrderCompatible_attachment
    [LT P]
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L.withOrder P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (hOld : PartiteOrderCompatible C)
    (hCore : PartiteOrderCompatible E) :
    PartiteOrderCompatible
      (StructuralRamsey.Partite.Attachment.attach C S E f) := by
  intro x y hxy
  change (StructuralRamsey.RelStructure.Attachment.attach
    C.toRelStructure S E.toRelStructure
    (fun i => (f i).toEmbedding)).rel (.inr ()) ![x, y] at hxy
  rcases hxy with ⟨z, hz, heq⟩ | ⟨i, z, hz, heq⟩
  · have hx : x = Sum.inl (z 0) := by
      have h := congrFun heq (0 : Fin 2)
      simpa using h
    have hy : y = Sum.inl (z 1) := by
      have h := congrFun heq (1 : Fin 2)
      simpa using h
    simpa [StructuralRamsey.Partite.Attachment.attach,
      StructuralRamsey.Partite.Attachment.part, hx, hy] using
      hCore (z 0) (z 1) hz
  · let W := StructuralRamsey.Partite.Attachment.attach C S E f
    have hx :
        x = StructuralRamsey.RelStructure.Attachment.copyMap
          C.toRelStructure S E.toRelStructure
          (fun j => (f j).toEmbedding) i (z 0) := by
      have h := congrFun heq (0 : Fin 2)
      simpa using h
    have hy :
        y = StructuralRamsey.RelStructure.Attachment.copyMap
          C.toRelStructure S E.toRelStructure
          (fun j => (f j).toEmbedding) i (z 1) := by
      have h := congrFun heq (1 : Fin 2)
      simpa using h
    calc
      W.part x = C.part (z 0) := by
        rw [hx]
        exact StructuralRamsey.Partite.Attachment.part_copyMap
          C S E f i (z 0)
      _ < C.part (z 1) := hOld (z 0) (z 1) hz
      _ = W.part y := by
        rw [hy]
        exact (StructuralRamsey.Partite.Attachment.part_copyMap
          C S E f i (z 1)).symm


/-- The local core is automatically compatible with the auxiliary
base order when all its parts lie above one ordered base A-copy and
the partite projection preserves the distinguished order relation.

The hypothesis on the base embedding says that its ORIGINAL order
agrees with the auxiliary base order on the chosen base copy.
No A-generation or local Ramsey hypothesis is used. -/
theorem partiteOrderCompatible_localOfBaseCopy
    {UA : Type v} [LinearOrder UA] [LT P]
    (A₀ : StructuralRamsey.RelStructure L UA)
    (D : StructuralRamsey.RelStructure L.withOrder P)
    (E : StructuralRamsey.Partite.System L.withOrder P Y)
    (hPartite : E.IsPartiteOver D)
    (α : StructuralRamsey.RelStructure.Embedding A₀.ordered D)
    (hα : ∀ u v : UA, u < v → α u < α v)
    (part : Y → UA)
    (hFine : ∀ y : Y, E.part y = α (part y)) :
    PartiteOrderCompatible E := by
  intro x y hxy
  have hBase := hPartite.map_rel hxy
  have hD : D.rel (.inr ()) ![α (part x), α (part y)] := by
    simpa [Function.comp_apply, hFine] using hBase
  have hA : part x < part y := by
    exact (α.map_rel_iff (.inr ()) ![part x, part y]).mp hD
  calc
    E.part x = α (part x) := hFine x
    _ < α (part y) := hα (part x) (part y) hA
    _ = E.part y := (hFine y).symm

end StructuralRamsey.Girth

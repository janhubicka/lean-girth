import Girth.ActivePicture
import PartiteConstruction.Relational.Order

/-!
# Compatibility of a partite picture with the auxiliary base order

The circulation proof maintains that an occurrence of the distinguished
binary order symbol in the picture projects forward along the fixed
auxiliary linear order of the Ramsey base. This is preserved under
the standard free picture attachment because every relation tuple
comes entirely from its local core or one old standard picture.

Both the gluing theorem and the local-core order argument are
independent of the local Ramsey arrow, foresthood and A-generation.
They require the base A-copy's original order to agree with the
auxiliary base order.
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
  ∀ z : Fin 2 → X,
    C.toRelStructure.rel (.inr ()) z →
      C.part (z 0) < C.part (z 1)

/-- A free picture attachment preserves compatibility with the
auxiliary base order, assuming compatibility of the old picture
and the new local core. -/
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
  let W := StructuralRamsey.Partite.Attachment.attach C S E f
  intro z hz
  change (StructuralRamsey.RelStructure.Attachment.attach
    C.toRelStructure S E.toRelStructure
    (fun i => (f i).toEmbedding)).rel (.inr ()) z at hz
  rcases hz with ⟨w, hw, hwz⟩ | ⟨i, w, hw, hwz⟩
  · subst z
    exact hCore w hw
  · subst z
    simpa only [Function.comp_apply,
      StructuralRamsey.Partite.Attachment.part_copyMap] using
      hOld w hw

/-- The local core is automatically compatible with the auxiliary
base order when its parts lie over one ordered base A-copy and the
original order of that copy agrees with the auxiliary base order.

No A-generation or local Ramsey hypothesis is needed. -/
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
  intro z hz
  have hBase := hPartite.map_rel hz
  have hFun : (E.part ∘ z) = α ∘ (part ∘ z) := by
    funext i
    exact hFine (z i)
  rw [hFun] at hBase
  have hLt : part (z 0) < part (z 1) :=
    (α.map_rel_iff (.inr ()) (part ∘ z)).mp hBase
  calc
    E.part (z 0) = α (part (z 0)) := hFine (z 0)
    _ < α (part (z 1)) := hα (part (z 0)) (part (z 1)) hLt
    _ = E.part (z 1) := (hFine (z 1)).symm

end StructuralRamsey.Girth

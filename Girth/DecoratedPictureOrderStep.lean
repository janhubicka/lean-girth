import Girth.PartiteOrderCompatibility
import Girth.DecorationPartiteBridge

/-!
# Auxiliary-order compatibility of the actual decorated local picture step

The circulation order invariant does not require A-generation of the
new local witness. A transversal high-girth support witness, decorated
by ordered A and relabelled by the processed base A-copy, is genuinely
partite over the base. Therefore each distinguished order tuple
projects to the original order on that A-copy. If the original and
auxiliary orders agree there, the new core is compatible.

The actual free picture attachment then inherits compatibility from
the old picture and this core. The whole argument is independent of
Ramsey colour transfer and the bounded-copy forest theorem, apart
from the high-girth geometric decoration already present.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I : Type v}

/-- Local order compatibility follows from the genuine high-girth
decoration, partite relabelling and the processed base order. -/
theorem decoratedLocalWitness_orderCompatible
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [LT P]
    (D : RelStructure L.withOrder P)
    (α : RelStructure.Embedding A₀.ordered D)
    (hα : ∀ u v : UA, u < v → α u < α v)
    {K : Set (Set Y)} {part : Y → UA}
    (hTrans : EdgeTransversal K part)
    (hGirth : GirthGT K 3)
    (hNonempty : K.Nonempty)
    (hCover : ∀ y : Y, ∃ e : Set Y, e ∈ K ∧ y ∈ e) :
    PartiteOrderCompatible
      ((decorateSupportSystem A₀.ordered K part hTrans).relabel
        α.toFunctionEmbedding) := by
  let E :=
    (decorateSupportSystem A₀.ordered K part hTrans).relabel
      α.toFunctionEmbedding
  have hPartite : E.IsPartiteOver D :=
    decorateSupportRelabel_isPartiteOver
      A₀.ordered
      (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
      hTrans hGirth hNonempty hCover D α
  exact partiteOrderCompatible_localOfBaseCopy
    A₀ D E hPartite α hα part (by intro y; rfl)

/-- The full standard picture extension preserves auxiliary-order
compatibility when its core is the actual decorated local-forest
witness. No A-generation or local Ramsey arrow is needed. -/
theorem pictureStep_orderCompatible_of_decoratedLocal
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [LT P]
    (D : RelStructure L.withOrder P)
    (α : RelStructure.Embedding A₀.ordered D)
    (hα : ∀ u v : UA, u < v → α u < α v)
    {K : Set (Set Y)} {part : Y → UA}
    (hTrans : EdgeTransversal K part)
    (hGirth : GirthGT K 3)
    (hNonempty : K.Nonempty)
    (hCover : ∀ y : Y, ∃ e : Set Y, e ∈ K ∧ y ∈ e)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (S : Set X)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S)
      ((decorateSupportSystem A₀.ordered K part hTrans).relabel
        α.toFunctionEmbedding))
    (hOld : PartiteOrderCompatible C) :
    PartiteOrderCompatible
      (StructuralRamsey.Partite.Attachment.attach C S
        ((decorateSupportSystem A₀.ordered K part hTrans).relabel
          α.toFunctionEmbedding) f) := by
  exact partiteOrderCompatible_attachment
    C S
    ((decorateSupportSystem A₀.ordered K part hTrans).relabel
      α.toFunctionEmbedding)
    f hOld
    (decoratedLocalWitness_orderCompatible
      A₀ D α hα hTrans hGirth hNonempty hCover)

end StructuralRamsey.Girth

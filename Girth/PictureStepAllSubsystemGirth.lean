import Girth.ProcessedActiveGirth
import Girth.UntouchedActiveGirth

/-!
# Preservation of girth for EVERY active subsystem of one picture step

The full girth clause of the circulation forest-completion invariant has
two cases for a base A-copy beta:

* beta = alpha, the processed projection. Every new projected A-copy
  lies in the local core and the active subsystem embeds into that
  core, inheriting its girth.
* beta != alpha, an untouched projection. Base A-linearity, bounded
  local-copy forests and transversal support exclude short cycles in
  the actual induced beta-active subsystem.

This packages the entire family of girth inequalities in one theorem
with the input conditions supplied by the structural local-forest
partite lemma. It DOES NOT establish existence of the local witness
or the remaining picture-step properties.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I Z : Type v}

/-- The girth clause of the standard picture-step invariant, for all
base A-copies simultaneously, assuming the honest local support
forest, local girth and true active gluing geometry. -/
theorem pictureStep_allActiveSubsystems_girthGT
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (α : RelStructure.Embedding A₀.ordered D)
    (E : StructuralRamsey.Partite.System L.withOrder P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A₀.ordered C α.toFunctionEmbedding)) E)
    (hPartite : C.IsPartiteOver D)
    (hEPartite : E.IsPartiteOver D)
    (hBaseLinear : ALinear A₀.ordered D)
    (u v : UA) (huv : u ≠ v)
    [Nonempty I]
    (part : Y → UA)
    (hFine : ∀ y, E.part y = α (part y))
    {H : Set (Set Z)} {K : Set (Set Y)}
    (family : I → StrongSupportEmbedding H K)
    (hTransK : EdgeTransversal K part)
    (g : ℕ)
    (hLocalForest :
      LocalForestThrough (fun i : I => (family i).supportPiece) g)
    (hCarrier :
      ∀ i : I,
        Set.range (family i) = copyCarrier ((f i).toEmbedding))
    (hLocalGirth : GirthGT (supportCopies A₀.ordered E.toRelStructure) g)
    (hOldGirth :
      ∀ β : RelStructure.Embedding A₀.ordered D,
        GirthGT
          (supportCopies A₀.ordered
            (C.induce
              (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toRelStructure)
          g) :
    ∀ β : RelStructure.Embedding A₀.ordered D,
      GirthGT
        (supportCopies A₀.ordered
          ((StructuralRamsey.Partite.Attachment.attach C
            (activeCarrier A₀.ordered C α.toFunctionEmbedding) E f).induce
              (activeCarrier A₀.ordered
                (StructuralRamsey.Partite.Attachment.attach C
                  (activeCarrier A₀.ordered C α.toFunctionEmbedding) E f)
                β.toFunctionEmbedding)).toRelStructure)
        g := by
  intro β
  by_cases hEq : β = α
  · subst β
    exact processed_activeSubsystem_girthGT_of_local
      A₀.ordered
      (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
      C α.toFunctionEmbedding E f g hLocalGirth
  · exact untouched_activeSubsystem_girthGT_of_transversal_local
      A₀ D C (activeCarrier A₀.ordered C α.toFunctionEmbedding)
      E f hPartite hEPartite hBaseLinear α β
      (Ne.symm hEq) u v huv part hFine family hTransK
      g hLocalForest hCarrier (hOldGirth β)

end StructuralRamsey.Girth

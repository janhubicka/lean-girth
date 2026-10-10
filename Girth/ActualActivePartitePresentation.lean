import Girth.ActualActiveSupportGeometry

/-!
# The true ordered active subsystem as an actual A-partite source

The active subsystem is an induced substructure of the original
D-partite picture, with part labels in beta[A]. Its A-coordinate is
the inverse beta part map from ActualActiveDecorationBridge.

The real active subsystem therefore has a canonical A-partite
structure ON ITS OWN TRUE VERTEX CARRIER, not on the larger union
of all selected base parts. Partite transversality follows directly
from the original picture's transversal relations and injectivity
of beta.

For finite ordered A, A-generation identifies the entire relational
source with the decoration of its actual full A-support; the
identity embedding preserves the canonical A-partite coordinates.
No high-girth or Ramsey assertion is needed for this equivalence.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X : Type v}

/-- Build the genuine A-partite source by restricting to vertices
lying in projected A-copies and inverting beta on their part labels. -/
noncomputable def actualActiveSubsystemPartite
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (beta : UA ↪ P) :
    StructuralRamsey.Partite.System L UA (activeCarrier A C beta) where
  toRelStructure := (C.induce (activeCarrier A C beta)).toRelStructure
  part := activeSourcePart A C beta
  transversal := by
    intro R z hz i j hPartEq
    change C.rel R (Subtype.val ∘ z) at hz
    have hEq : C.part (z i).val = C.part (z j).val := by
      calc
        C.part (z i).val =
          beta (activeSourcePart A C beta (z i)) :=
          (activeSourcePart_spec A C beta (z i)).symm
        _ = beta (activeSourcePart A C beta (z j)) :=
          congrArg beta hPartEq
        _ = C.part (z j).val :=
          activeSourcePart_spec A C beta (z j)
    apply Subtype.ext
    exact C.transversal R (Subtype.val ∘ z) hz i j hEq

/-- The genuine ordered A-partite active source embeds BY THE IDENTITY
in the decoration of its full A-support. No extraneous support
hypergraph or relabelled carrier is introduced. -/
def actualActiveSubsystem_toDecorated
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hPartite : C.IsPartiteOver D)
    (beta : RelStructure.Embedding A₀.ordered D)
    (hGen : AGenerated A₀.ordered
      (C.induce
        (activeCarrier A₀.ordered C beta.toFunctionEmbedding)).toRelStructure) :
    StructuralRamsey.Partite.Embedding
      (actualActiveSubsystemPartite A₀.ordered C beta.toFunctionEmbedding)
      (decorateSupportSystem A₀.ordered
        (supportCopies A₀.ordered
          (C.induce
            (activeCarrier A₀.ordered C beta.toFunctionEmbedding)).toRelStructure)
        (activeSourcePart A₀.ordered C beta.toFunctionEmbedding)
        (actualActiveSupport_edgeTransversal A₀ D C hPartite beta)) where
  toEmbedding := {
    toFun := id
    injective := fun _ _ h => h
    map_rel_iff := by
      intro R z
      change
        (decorateSupport A₀.ordered
          (supportCopies A₀.ordered
            (C.induce
              (activeCarrier A₀.ordered C beta.toFunctionEmbedding)).toRelStructure)
          (activeSourcePart A₀.ordered C beta.toFunctionEmbedding)).rel R z ↔
        (C.induce
          (activeCarrier A₀.ordered C beta.toFunctionEmbedding)).toRelStructure.rel R z
      exact (actualActiveSubsystem_relation_iff_decorated
        A₀ D C hPartite beta hGen R z).symm
  }
  map_part _ := rfl

end StructuralRamsey.Girth

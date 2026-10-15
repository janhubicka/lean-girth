import Girth.TrainBoundaryPairCoreSupport

/-!
# Circulation: a standard physical A-edge through two core vertices

The general two-standard proof invokes the active-boundary dichotomy
twice: for the designated copy that becomes supreme, AND for an old
ambient physical A-edge through its two vertex connectors. The latter
needs the A-copy specialization, not a vague appeal to base linearity.

In an A-linear base, the projected A-copy is A-strong. Thus the
already checked designated-copy boundary theorem, specialized to B=A,
says that any two distinct points of a standard A-copy lying in the
core also belong to a genuine CORE A-copy. In particular they give
a real core A-support edge containing both.

This only proves the geometric old-edge -> core-edge transfer.
It does NOT assert the four-occurrence word is acceptable, supply a
supreme-copy plan, or prove the unrestricted two-standard lemma.
No appendix statements or source files are touched.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I : Type v}

/-- Any old physical A-copy in a standard attachment containing two
different actual core vertices forces an A-copy in the core through
that pair. Requires only A-linearity of the base. -/
theorem attachedProjectedACopy_two_core_vertices_have_coreACopy
    (A : RelStructure L UA)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (e b : RelStructure.Embedding A D)
    (q : StructuralRamsey.Partite.ProjectedEmbedding A C b)
    (hLinear : ALinear A D)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (i : I)
    (x y : RelStructure.Attachment.Vertex
      (activeCarrier A C e.toFunctionEmbedding) (W := Y) (I := I))
    (hxy : x ≠ y) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let copyI :=
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
    let core :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    x ∈ copyCarrier (copyI.comp q.val) →
    y ∈ copyCarrier (copyI.comp q.val) →
    x ∈ copyCarrier core →
    y ∈ copyCarrier core →
    ∃ aCore : RelStructure.Embedding A E.toRelStructure,
      x ∈ copyCarrier (core.comp aCore) ∧
      y ∈ copyCarrier (core.comp aCore) := by
  exact attachedProjectedCopy_two_core_vertices_have_coreACopy
    A A D C e b q
    (aStrong_copyCarrier_of_aLinear hLinear b)
    E f i x y hxy

end StructuralRamsey.Girth

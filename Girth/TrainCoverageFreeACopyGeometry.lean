import Girth.TrainCoverageFreeACopyProjection
import Girth.ActiveSupportProjectionExact
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Strong gluing geometry and exact active support from weak A-copy projection

The proofs of active strongness, standard-copy strongness, A-linearity,
and identification of true active support with projected support only
need the base images of actual physical A-copies.

No full order-expanded IsPartiteOver assumption is used here. The
auxiliary order may create irreducible sets unsupported by A-edges.

These are source candidates awaiting exact-head Lean elaboration.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X Y I : Type v}

/-- The usual picture geometry from projected physical A-copies
without requiring projection of all order-irreducibles. -/
theorem activeAttachment_geometry_of_projectedACopies
    (A : RelStructure L UA)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hA : A.Irreducible)
    (hProjected : ProjectsACopies A D C)
    (hBaseLinear : ALinear A D)
    (e : Embedding A D)
    (hRigid : ∀ b : Embedding A D, SameCopy b e → b = e)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (hOldLinear : ALinear A C.toRelStructure)
    (hCoreLinear : ALinear A E.toRelStructure)
    (hImage : ∀ i : I,
      AStrong A E.toRelStructure
        (copyCarrier (f i).toEmbedding)) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let T := StructuralRamsey.Partite.Attachment.attach C S E f
    ALinear A T.toRelStructure ∧
      ∀ i : I,
        AStrong A T.toRelStructure
          (copyCarrier
            (StructuralRamsey.Partite.Attachment.copyEmbedding
              C S E f i).toEmbedding) := by
  let S := activeCarrier A C e.toFunctionEmbedding
  have hS : AStrong A C.toRelStructure S :=
    activeCarrier_aStrong_of_projectedACopies
      A D C hProjected hBaseLinear e hRigid
  constructor
  · exact attachment_aLinear
      C.toRelStructure S E.toRelStructure
      (fun i => (f i).toEmbedding)
      hA hOldLinear hCoreLinear hS hImage
  · intro i
    exact attachment_copy_aStrong
      C.toRelStructure S E.toRelStructure
      (fun i => (f i).toEmbedding)
      hA hS hImage i

/-- Any genuine A-copy inside the true active induced subsystem
still projects to the exact processed ordered base copy.
No full IsPartiteOver invariant or base A-linearity is required. -/
theorem activeInduced_ACopy_projects_of_projectedACopies
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hProjected : ProjectsACopies A₀.ordered D C)
    (β : Embedding A₀.ordered D)
    (a : Embedding A₀.ordered
      (C.induce
        (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toRelStructure) :
    ∃ proj : StructuralRamsey.Partite.ProjectedEmbedding
        A₀.ordered C β.toFunctionEmbedding,
      ∀ u : UA,
        proj.val u =
          ((StructuralRamsey.Partite.System.inclusion C
            (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toEmbedding.comp a) u := by
  classical
  let S := activeCarrier A₀.ordered C β.toFunctionEmbedding
  let inc : Embedding
      (C.induce S).toRelStructure C.toRelStructure :=
    (StructuralRamsey.Partite.System.inclusion C S).toEmbedding
  let aWhole : Embedding A₀.ordered C.toRelStructure :=
    inc.comp a
  obtain ⟨b, hb⟩ := hProjected aWhole
  have hBaseRange (u : UA) : ∃ v : UA, b u = β v := by
    obtain ⟨e, ⟨v, hv⟩⟩ := (a u).property
    refine ⟨v, ?_⟩
    calc
      b u = C.part (aWhole u) := hb u
      _ = C.part (e.val v) := congrArg C.part hv.symm
      _ = β v := e.property v
  have hSame : SameCopy b β :=
    sameCopy_of_range_subset b β hBaseRange
  have hbEq : b = β :=
    ordered_embedding_eq_of_sameCopy b β hSame
  let proj : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered C β.toFunctionEmbedding := {
    val := aWhole
    property := by
      intro u
      have h := hb u
      rw [hbEq] at h
      exact h.symm
  }
  exact ⟨proj, by intro u; rfl⟩

/-- Even if the ambient auxiliary order creates unrelated
irreducible sets, the actual induced support is exactly the
family of physical A-edges with the prescribed base projection. -/
theorem mapped_activeSupport_eq_projected_of_projectedACopies
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hProjected : ProjectsACopies A₀.ordered D C)
    (β : Embedding A₀.ordered D) :
    mappedSupportCopies A₀.ordered
      (C.induce
        (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toRelStructure
      C.toRelStructure
      (StructuralRamsey.Partite.System.inclusion C
        (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toEmbedding
      =
    projectedSupportCopies A₀.ordered C β.toFunctionEmbedding := by
  apply Set.Subset.antisymm
  · intro T hT
    obtain ⟨a, hEq⟩ := hT
    obtain ⟨proj, hProj⟩ :=
      activeInduced_ACopy_projects_of_projectedACopies
        A₀ D C hProjected β a
    refine ⟨proj, ?_⟩
    have heq :
        ((StructuralRamsey.Partite.System.inclusion C
          (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toEmbedding.comp a) =
          proj.val := by
      apply Embedding.ext
      intro u
      exact (hProj u).symm
    calc
      T = copyCarrier
          ((StructuralRamsey.Partite.System.inclusion C
            (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toEmbedding.comp a) := hEq
      _ = copyCarrier proj.val := congrArg copyCarrier heq
  · exact projectedSupportCopies_subset_mapped_activeSupport
      A₀.ordered C β.toFunctionEmbedding

end StructuralRamsey.Girth

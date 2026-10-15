import Girth.ActiveBoundary

/-!
# Circulation: two core-boundary vertices yield one core A-support copy

The existing active-boundary dichotomy says that a projected designated
B-copy, transported into a standard attached picture, meets the local
core in at most one vertex or precisely one transported A-copy.

If two distinct boundary vertices x,y lie in that designated B-copy
AND in the core, the first alternative is impossible. The resulting
whole A-copy has its image in the core and hence factors through the
core embedding. Thus there exists a GENUINE core A-support copy
containing both boundary vertices, not just an old ambient edge or an
unlabelled pair. This is the exact geometric consequence used at the
end of the circulation general two-standard obstruction.

The result reuses the proven active-boundary classification and does
not require output-wagon linearity, cyclic replacement legality or
any appendix statement.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- If a transported projected B-copy meets the actual local core in
two distinct points, a genuine core A-copy through both points exists.
The conclusion names the real A-embedding into the core witness. -/
theorem attachedProjectedCopy_two_core_vertices_have_coreACopy
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (e : RelStructure.Embedding A D)
    (b : RelStructure.Embedding B D)
    (q : StructuralRamsey.Partite.ProjectedEmbedding B C b)
    (hStrong : AStrong A D (copyCarrier b))
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
  dsimp only
  intro hxCopy hyCopy hxCore hyCore
  let S := activeCarrier A C e.toFunctionEmbedding
  let copyI :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  let core :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  rcases
      attachedProjectedCopy_core_intersection_classify
        A B D C e b q hStrong E f i with
    hSmall | ⟨aB, hEq⟩
  · exact False.elim (hxy
      (hSmall ⟨hxCopy, hxCore⟩ ⟨hyCopy, hyCore⟩))
  · let lifted := copyI.comp (q.val.comp aB)
    have hLiftInCore (a : UA) :
        lifted a ∈ copyCarrier core := by
      have h : lifted a ∈
          copyCarrier (copyI.comp q.val) ∩ copyCarrier core := by
        rw [hEq]
        exact ⟨a, rfl⟩
      exact h.2
    have hFactor : ∀ a : UA, ∃ z : Y, lifted a = core z := by
      intro a
      obtain ⟨z, hz⟩ := hLiftInCore a
      exact ⟨z, hz.symm⟩
    let aCore : RelStructure.Embedding A E.toRelStructure :=
      lifted.factorThroughRange core hFactor
    have hComm (a : UA) : lifted a = core (aCore a) :=
      Classical.choose_spec (hFactor a)
    have hxLift : x ∈ copyCarrier lifted := by
      change x ∈ copyCarrier (copyI.comp (q.val.comp aB))
      rw [← hEq]
      exact ⟨hxCopy, hxCore⟩
    have hyLift : y ∈ copyCarrier lifted := by
      change y ∈ copyCarrier (copyI.comp (q.val.comp aB))
      rw [← hEq]
      exact ⟨hyCopy, hyCore⟩
    refine ⟨aCore, ?_, ?_⟩
    · obtain ⟨a, ha⟩ := hxLift
      exact ⟨a, (hComm a).symm.trans ha⟩
    · obtain ⟨a, ha⟩ := hyLift
      exact ⟨a, (hComm a).symm.trans ha⟩

end StructuralRamsey.Girth

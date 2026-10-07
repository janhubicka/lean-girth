import Girth.ActivePicture
import Girth.UntouchedOwner

/-! # Factoring untouched copies through the old active subsystem

If a projected A-copy in one standard picture has projection beta, then after
factoring through that standard picture its preimage is a beta-projected
A-copy in the old picture. Hence it lies in the true beta-active subsystem.
This is the constant-owner pullback used by the circulation girth proof.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I : Type v}

/-- Factor a projected A-copy through a standard copy containing its whole
carrier, retaining its projection beta. -/
noncomputable def projectedFactorThroughStandard
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (β : UA ↪ P)
    (i : I)
    (a : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Attachment.attach C S E f) β)
    (hSub :
      copyCarrier a.val ⊆
        copyCarrier
          (StructuralRamsey.Partite.Attachment.copyEmbedding
            C S E f i).toEmbedding) :
    StructuralRamsey.Partite.ProjectedEmbedding A C β := by
  classical
  let std :=
    StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i
  have hFactor : ∀ u : UA, ∃ x : X, a.val u = std x := by
    intro u
    rcases hSub ⟨u, rfl⟩ with ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  let eC : RelStructure.Embedding A C.toRelStructure :=
    a.val.factorThroughRange std.toEmbedding hFactor
  refine
    { val := eC
      property := ?_ }
  intro u
  have hspec :
      std (eC u) = a.val u := by
    change
      std (Classical.choose (hFactor u)) = a.val u
    exact (Classical.choose_spec (hFactor u)).symm
  calc
    C.part (eC u) =
        (StructuralRamsey.Partite.Attachment.attach C S E f).part
          (std (eC u)) := (std.map_part (eC u)).symm
    _ =
        (StructuralRamsey.Partite.Attachment.attach C S E f).part
          (a.val u) := congrArg
            (StructuralRamsey.Partite.Attachment.attach C S E f).part
            hspec
    _ = β u := a.property u

/-- The factorization through the standard copy really recovers the original
ambient A-copy pointwise. -/
theorem projectedFactorThroughStandard_spec
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (β : UA ↪ P)
    (i : I)
    (a : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Attachment.attach C S E f) β)
    (hSub :
      copyCarrier a.val ⊆
        copyCarrier
          (StructuralRamsey.Partite.Attachment.copyEmbedding
            C S E f i).toEmbedding)
    (u : UA) :
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i)
        ((projectedFactorThroughStandard
          A C S E f β i a hSub).val u) =
      a.val u := by
  classical
  let std :=
    StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i
  have hFactor : ∀ x : UA, ∃ y : X, a.val x = std y := by
    intro x
    rcases hSub ⟨x, rfl⟩ with ⟨y, hy⟩
    exact ⟨y, hy.symm⟩
  change std (Classical.choose (hFactor u)) = a.val u
  exact (Classical.choose_spec (hFactor u)).symm

/-- The standard embedding restricted to the old beta-active subsystem. -/
noncomputable def standardActiveEmbedding
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (β : UA ↪ P)
    (i : I) :
    StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C β))
      (StructuralRamsey.Partite.Attachment.attach C S E f) :=
  (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).comp
    (StructuralRamsey.Partite.System.inclusion C (activeCarrier A C β))

/-- A beta-projected A-copy contained in standard copy i is in fact contained
in the beta-active restriction of standard copy i. -/
theorem projectedCopy_subset_standardActive
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (β : UA ↪ P)
    (i : I)
    (a : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Attachment.attach C S E f) β)
    (hSub :
      copyCarrier a.val ⊆
        copyCarrier
          (StructuralRamsey.Partite.Attachment.copyEmbedding
            C S E f i).toEmbedding) :
    copyCarrier a.val ⊆
      copyCarrier
        (standardActiveEmbedding A C S E f β i).toEmbedding := by
  intro z hz
  rcases hz with ⟨u, rfl⟩
  let aC :=
    projectedFactorThroughStandard A C S E f β i a hSub
  let xu : activeCarrier A C β :=
    ⟨aC.val u, projected_mem_activeCarrier A C β aC u⟩
  refine ⟨xu, ?_⟩
  change
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i)
        (aC.val u) = a.val u
  exact projectedFactorThroughStandard_spec
    A C S E f β i a hSub u

end StructuralRamsey.Girth

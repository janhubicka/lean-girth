import Girth.TrainRecursiveRigidPartiteArrow
import Girth.TrainRecursiveStrongSupportedHJBase

set_option autoImplicit false
set_option Elab.async false

/-!
# Genuine designated relational Ramsey arrows from the partite HJ family

The q>2 recursive lower target is a genuine A-partite relational
structure and the larger HJ Ramsey base provides a PARTITE arrow.
The finite forest-tail picture pass instead consumes a RELATIONAL
designated-base arrow: it must colour ALL relational copies of A,
and the monochromatic B-copy must belong to the ACTUAL prescribed
family of Hales--Jewett line embeddings.

For ordered finite A, irreducibility and rigidity show that each
relational A-copy in the source is automatically part-preserving.
Consequently the line-family partite arrow supplies exactly the
relational family arrow without changing its chosen line, its
selected label, or any physical A-edge.

This removes the lower BASE arrow as an independent input. The later
geometric local picture steps, the selected lower witness arrow
after the whole finite pass, and the attached-output
SupremeCycleBound are not constructed here. No appendix.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {Q V X : Type v}

/-- Upgrade a PARTITE Ramsey arrow with an explicit designated-family
membership certificate to a RELATIONAL designated-base arrow.
This retains the chosen prescribed B-copy instead of replacing it by
an arbitrary partite embedding supplied by an abstract Arrow theorem. -/
theorem relationalDesignatedArrow_of_partiteFamily_for_orderedA
    (A₀ : RelStructure L Q) [LinearOrder Q] [Finite Q]
    (B : StructuralRamsey.Partite.System L.withOrder Q V)
    (D : StructuralRamsey.Partite.System L.withOrder Q X)
    (family : Set (Embedding B.toRelStructure D.toRelStructure))
    (hB : B.IsPartiteOver A₀.ordered)
    (κ : Type w)
    (hPartiteFamily :
      ∀ χ : StructuralRamsey.Partite.Embedding
          (StructuralRamsey.Partite.transversal A₀.ordered) D → κ,
        ∃ b : StructuralRamsey.Partite.Embedding B D,
          b.toEmbedding ∈ family ∧
          ∀ a₁ a₂ : StructuralRamsey.Partite.Embedding
            (StructuralRamsey.Partite.transversal A₀.ordered) B,
              χ (b.comp a₁) = χ (b.comp a₂)) :
    ∀ χ : Embedding A₀.ordered D.toRelStructure → κ,
      ∃ b : Embedding B.toRelStructure D.toRelStructure,
        b ∈ family ∧
        ∀ a₁ a₂ : Embedding A₀.ordered B.toRelStructure,
          χ (b.comp a₁) = χ (b.comp a₂) := by
  intro χ
  obtain ⟨b, hb, hMono⟩ := hPartiteFamily (fun e => χ e.toEmbedding)
  refine ⟨b.toEmbedding, hb, ?_⟩
  intro a₁ a₂
  let hIrr : A₀.ordered.Irreducible :=
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  let hRigid : ∀ a : Embedding A₀.ordered A₀.ordered,
      a = Embedding.id A₀.ordered :=
    fun a => orderedA_self_embedding_is_id A₀ a
  let a₁' := relationalA_embedding_to_partite_of_rigid
    A₀.ordered B hIrr hB hRigid a₁
  let a₂' := relationalA_embedding_to_partite_of_rigid
    A₀.ordered B hIrr hB hRigid a₂
  exact hMono a₁' a₂'

/-- The ACTUAL Hales--Jewett line family, rather than a larger
unspecified embedding family, gives the required relational
designated-base arrow on finite ordered A. The chosen witness is
literally a genuine line embedding with its prescribed family label. -/
theorem HJLineFamily.relationalDesignatedBaseArrow
    (A₀ : RelStructure L Q) [LinearOrder Q] [Finite Q]
    (B : StructuralRamsey.Partite.System L.withOrder Q V)
    (hB : B.IsPartiteOver A₀.ordered)
    (N : ℕ)
    (family : Set (Embedding B.toRelStructure
      (StructuralRamsey.Partite.Induced.power B N).toRelStructure))
    (κ : Type w)
    (hLineArrow :
      ∀ χ : StructuralRamsey.Partite.Embedding
          (StructuralRamsey.Partite.transversal A₀.ordered)
          (StructuralRamsey.Partite.Induced.power B N) → κ,
        ∃ W : HalesJewett.Line
            (StructuralRamsey.Partite.Induced.Letter A₀.ordered B) N,
          (StructuralRamsey.Partite.Induced.lineEmbedding hB W).toEmbedding ∈
            family ∧
          ∀ a₁ a₂ : StructuralRamsey.Partite.Embedding
              (StructuralRamsey.Partite.transversal A₀.ordered) B,
            χ ((StructuralRamsey.Partite.Induced.lineEmbedding hB W).comp a₁) =
              χ ((StructuralRamsey.Partite.Induced.lineEmbedding hB W).comp a₂)) :
    ∀ χ : Embedding A₀.ordered
        (StructuralRamsey.Partite.Induced.power B N).toRelStructure → κ,
      ∃ b : Embedding B.toRelStructure
          (StructuralRamsey.Partite.Induced.power B N).toRelStructure,
        b ∈ family ∧
        ∀ a₁ a₂ : Embedding A₀.ordered B.toRelStructure,
          χ (b.comp a₁) = χ (b.comp a₂) := by
  apply relationalDesignatedArrow_of_partiteFamily_for_orderedA
    A₀ B (StructuralRamsey.Partite.Induced.power B N)
    family hB κ
  intro χ
  obtain ⟨W, hW, hMono⟩ := hLineArrow χ
  exact ⟨StructuralRamsey.Partite.Induced.lineEmbedding hB W, hW, hMono⟩

end StructuralRamsey.Girth

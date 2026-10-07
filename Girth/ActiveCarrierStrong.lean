import Girth.ActivePicture
import Girth.DesignatedPicture
import Girth.AttachmentLinearity
import PartiteConstruction.Partite.Induced

/-! # Strongness of the true active subsystem

The induced picture construction glues only along the true active carrier:
vertices lying in an A-copy with one prescribed base projection.  When the
base support is A-linear and that projection is rigid, this carrier is
A-strong.  This is the manuscript's implicit input to the attachment
linearity argument.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X : Type v}

/-- In an A-linear base, the true active carrier over a rigid base copy is
A-strong in the picture.  Rigidity means that two base A-embeddings with the
same image and one fixed target copy are equal; the ordered specialization
below supplies it automatically. -/
theorem activeCarrier_aStrong_of_base_aLinear
    (A : RelStructure L UA)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hA : A.Irreducible)
    (hPartite : C.IsPartiteOver D)
    (hLinear : ALinear A D)
    (e : RelStructure.Embedding A D)
    (hRigid :
      ∀ b : RelStructure.Embedding A D,
        SameCopy b e → b = e) :
    AStrong A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) := by
  classical
  intro a hMeet
  obtain ⟨b, hb⟩ :=
    hPartite.after_irreducible_embedding hA a
  have hBaseMeet :
      ¬(copyCarrier b ∩ copyCarrier e).Subsingleton := by
    rw [Set.not_subsingleton_iff] at hMeet ⊢
    rcases hMeet with ⟨x, hx, y, hy, hxy⟩
    rcases hx.1 with ⟨ax, hax⟩
    rcases hy.1 with ⟨ay, hay⟩
    have hxE : C.part x ∈ copyCarrier e :=
      activeCarrier_part_in_baseCopy A D C e hx.2
    have hyE : C.part y ∈ copyCarrier e :=
      activeCarrier_part_in_baseCopy A D C e hy.2
    have hbx : b ax = C.part x := by
      calc
        b ax = C.part (a ax) := hb ax
        _ = C.part x := congrArg C.part hax
    have hby : b ay = C.part y := by
      calc
        b ay = C.part (a ay) := hb ay
        _ = C.part y := congrArg C.part hay
    have hbxy : b ax ≠ b ay := by
      intro h
      have haxy : ax = ay := b.injective h
      apply hxy
      calc
        x = a ax := hax.symm
        _ = a ay := congrArg a haxy
        _ = y := hay
    refine ⟨b ax, ?_, b ay, ?_, hbxy⟩
    · constructor
      · exact ⟨ax, rfl⟩
      · rw [hbx]
        exact hxE
    · constructor
      · exact ⟨ay, rfl⟩
      · rw [hby]
        exact hyE
  have hSame : SameCopy b e := by
    by_contra hne
    exact hBaseMeet (hLinear b e hne)
  have hbe : b = e := hRigid b hSame
  let aProjected :
      StructuralRamsey.Partite.ProjectedEmbedding
        A C e.toFunctionEmbedding :=
    { val := a
      property := by
        intro u
        have h := hb u
        rw [hbe] at h
        exact h.symm }
  intro z hz
  rcases hz with ⟨u, rfl⟩
  exact ⟨aProjected, u, rfl⟩

/-- Ordered structures are rigid, so the manuscript's standard ordered
setting needs no extra rigidity hypothesis. -/
theorem activeCarrier_aStrong_ordered
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hPartite : C.IsPartiteOver D)
    (hLinear : ALinear A₀.ordered D)
    (e : RelStructure.Embedding A₀.ordered D) :
    AStrong A₀.ordered C.toRelStructure
      (activeCarrier A₀.ordered C e.toFunctionEmbedding) := by
  apply activeCarrier_aStrong_of_base_aLinear
    A₀.ordered D C
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
    hPartite hLinear e
  intro b hb
  exact ordered_embedding_eq_of_sameCopy b e hb


/-- Geometry package for one active attachment.  Strongness of the true
active carrier reduces the manuscript's standard-copy strongness and global
A-linearity clauses to the generic attachment theorems. -/
theorem activeAttachment_geometry_of_base_aLinear
    (A : RelStructure L UA)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hA : A.Irreducible)
    (hPartite : C.IsPartiteOver D)
    (hBaseLinear : ALinear A D)
    (e : RelStructure.Embedding A D)
    (hRigid :
      ∀ b : RelStructure.Embedding A D,
        SameCopy b e → b = e)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (hOldLinear : ALinear A C.toRelStructure)
    (hCoreLinear : ALinear A E.toRelStructure)
    (hImage :
      ∀ i : I,
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
    activeCarrier_aStrong_of_base_aLinear
      A D C hA hPartite hBaseLinear e hRigid
  constructor
  · exact
      attachment_aLinear
        C.toRelStructure S E.toRelStructure
        (fun i => (f i).toEmbedding)
        hA hOldLinear hCoreLinear hS hImage
  · intro i
    exact
      attachment_copy_aStrong
        C.toRelStructure S E.toRelStructure
        (fun i => (f i).toEmbedding)
        hA hS hImage i

/-- Ordered specialization of the active-attachment geometry package. -/
theorem activeAttachment_geometry_ordered
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hPartite : C.IsPartiteOver D)
    (hBaseLinear : ALinear A₀.ordered D)
    (e : RelStructure.Embedding A₀.ordered D)
    (E : StructuralRamsey.Partite.System L.withOrder P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce
        (activeCarrier A₀.ordered C e.toFunctionEmbedding)) E)
    (hOldLinear : ALinear A₀.ordered C.toRelStructure)
    (hCoreLinear : ALinear A₀.ordered E.toRelStructure)
    (hImage :
      ∀ i : I,
        AStrong A₀.ordered E.toRelStructure
          (copyCarrier (f i).toEmbedding)) :
    let S := activeCarrier A₀.ordered C e.toFunctionEmbedding
    let T := StructuralRamsey.Partite.Attachment.attach C S E f
    ALinear A₀.ordered T.toRelStructure ∧
      ∀ i : I,
        AStrong A₀.ordered T.toRelStructure
          (copyCarrier
            (StructuralRamsey.Partite.Attachment.copyEmbedding
              C S E f i).toEmbedding) := by
  apply activeAttachment_geometry_of_base_aLinear
    A₀.ordered D C
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
    hPartite hBaseLinear e
  · intro b hb
    exact ordered_embedding_eq_of_sameCopy b e hb
  · exact hOldLinear
  · exact hCoreLinear
  · exact hImage

end StructuralRamsey.Girth

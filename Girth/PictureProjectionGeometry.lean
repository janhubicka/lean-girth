import Girth.AttachmentGeometry

/-! # Projection geometry of distinct standard copies

The manuscript's picture lemma uses one further consequence of the free
attachment geometry.  Distinct standard copies can meet only through the
gluing subsystem.  Hence, when the gluing subsystem lies over one base
A-copy, every shared vertex projects into that base copy.  Combining this
with A-linearity of the base rules out a common A-copy in any other fibre.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P V W I : Type v}

/-- If two distinct standard copies identify old-picture vertices, then the
preimage in either old copy belongs to the gluing subsystem. -/
theorem shared_standard_copy_preimage_mem_glue
    (B : StructuralRamsey.Partite.System L P V)
    (S : Set V)
    (D : StructuralRamsey.Partite.System L P W)
    (f : I → StructuralRamsey.Partite.Embedding (B.induce S) D)
    {i j : I} (hij : i ≠ j)
    {x y : V}
    (hxy :
      StructuralRamsey.Partite.Attachment.copyEmbedding B S D f i x =
        StructuralRamsey.Partite.Attachment.copyEmbedding B S D f j y) :
    x ∈ S := by
  by_contra hx
  apply hij
  exact
    RelStructure.Attachment.index_eq_of_outside
      (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
      (f := fun k => (f k).toEmbedding) hx hxy

/-- If the gluing subsystem lies over the selected base copy `alpha`, then
every vertex shared by two distinct standard copies projects into
`range alpha`. -/
theorem shared_standard_copy_part_mem_active_support
    (B : StructuralRamsey.Partite.System L P V)
    (S : Set V)
    (D : StructuralRamsey.Partite.System L P W)
    (f : I → StructuralRamsey.Partite.Embedding (B.induce S) D)
    (α : UA ↪ P)
    (hS : S ⊆ B.support α)
    {i j : I} (hij : i ≠ j)
    {x y : V}
    (hxy :
      StructuralRamsey.Partite.Attachment.copyEmbedding B S D f i x =
        StructuralRamsey.Partite.Attachment.copyEmbedding B S D f j y) :
    B.part x ∈ Set.range α :=
  hS (shared_standard_copy_preimage_mem_glue B S D f hij hxy)

/-- Consequently, if the same shared vertex lies in an untouched fibre
`beta`, its base part lies in `range alpha ∩ range beta`. -/
theorem shared_standard_copy_part_mem_base_intersection
    (B : StructuralRamsey.Partite.System L P V)
    (S : Set V)
    (D : StructuralRamsey.Partite.System L P W)
    (f : I → StructuralRamsey.Partite.Embedding (B.induce S) D)
    (α β : UA ↪ P)
    (hS : S ⊆ B.support α)
    {i j : I} (hij : i ≠ j)
    {x y : V}
    (hxy :
      StructuralRamsey.Partite.Attachment.copyEmbedding B S D f i x =
        StructuralRamsey.Partite.Attachment.copyEmbedding B S D f j y)
    (hxβ : B.part x ∈ Set.range β) :
    B.part x ∈ Set.range α ∩ Set.range β :=
  ⟨shared_standard_copy_part_mem_active_support
      B S D f α hS hij hxy, hxβ⟩

/-- If the selected and untouched base fibres meet in at most one part, then
no projected copy with at least two specified vertices can be contained in two
distinct standard copies.

This is the no-common-A-copy clause in the manuscript's picture lemma, stated
with the two distinct source vertices explicitly so it does not need a
`Nontrivial` typeclass. -/
theorem no_common_projected_copy_of_subsingleton_base_intersection
    (A : RelStructure L UA)
    (B : StructuralRamsey.Partite.System L P V)
    (S : Set V)
    (D : StructuralRamsey.Partite.System L P W)
    (f : I → StructuralRamsey.Partite.Embedding (B.induce S) D)
    (α β : UA ↪ P)
    (hS : S ⊆ B.support α)
    (hInter : (Set.range α ∩ Set.range β).Subsingleton)
    {i j : I} (hij : i ≠ j)
    (e : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Attachment.attach B S D f) β)
    (hi :
      copyCarrier e.val ⊆
        copyCarrier
          (StructuralRamsey.Partite.Attachment.copyEmbedding
            B S D f i).toEmbedding)
    (hj :
      copyCarrier e.val ⊆
        copyCarrier
          (StructuralRamsey.Partite.Attachment.copyEmbedding
            B S D f j).toEmbedding)
    (a b : UA) (hab : a ≠ b) :
    False := by
  have hai := hi (show e.val a ∈ copyCarrier e.val from ⟨a, rfl⟩)
  have haj := hj (show e.val a ∈ copyCarrier e.val from ⟨a, rfl⟩)
  rcases hai with ⟨xa, hxa⟩
  rcases haj with ⟨ya, hya⟩
  have hxyA :
      StructuralRamsey.Partite.Attachment.copyEmbedding B S D f i xa =
        StructuralRamsey.Partite.Attachment.copyEmbedding B S D f j ya :=
    hxa.trans hya.symm
  have haα : B.part xa ∈ Set.range α :=
    shared_standard_copy_part_mem_active_support
      B S D f α hS hij hxyA
  have haPart : B.part xa = β a := by
    calc
      B.part xa =
          (StructuralRamsey.Partite.Attachment.attach B S D f).part
            (StructuralRamsey.Partite.Attachment.copyEmbedding B S D f i xa) :=
        (StructuralRamsey.Partite.Attachment.copyEmbedding
          B S D f i).map_part xa |>.symm
      _ =
          (StructuralRamsey.Partite.Attachment.attach B S D f).part
            (e.val a) :=
        congrArg
          (StructuralRamsey.Partite.Attachment.attach B S D f).part hxa
      _ = β a := e.property a
  rw [haPart] at haα
  have ha :
      β a ∈ Set.range α ∩ Set.range β :=
    ⟨haα, ⟨a, rfl⟩⟩

  have hbi := hi (show e.val b ∈ copyCarrier e.val from ⟨b, rfl⟩)
  have hbj := hj (show e.val b ∈ copyCarrier e.val from ⟨b, rfl⟩)
  rcases hbi with ⟨xb, hxb⟩
  rcases hbj with ⟨yb, hyb⟩
  have hxyB :
      StructuralRamsey.Partite.Attachment.copyEmbedding B S D f i xb =
        StructuralRamsey.Partite.Attachment.copyEmbedding B S D f j yb :=
    hxb.trans hyb.symm
  have hbα : B.part xb ∈ Set.range α :=
    shared_standard_copy_part_mem_active_support
      B S D f α hS hij hxyB
  have hbPart : B.part xb = β b := by
    calc
      B.part xb =
          (StructuralRamsey.Partite.Attachment.attach B S D f).part
            (StructuralRamsey.Partite.Attachment.copyEmbedding B S D f i xb) :=
        (StructuralRamsey.Partite.Attachment.copyEmbedding
          B S D f i).map_part xb |>.symm
      _ =
          (StructuralRamsey.Partite.Attachment.attach B S D f).part
            (e.val b) :=
        congrArg
          (StructuralRamsey.Partite.Attachment.attach B S D f).part hxb
      _ = β b := e.property b
  rw [hbPart] at hbα
  have hb :
      β b ∈ Set.range α ∩ Set.range β :=
    ⟨hbα, ⟨b, rfl⟩⟩

  have hβab : β a = β b :=
    hInter ha hb
  exact hab (β.injective hβab)

/-- Base A-linearity supplies the subsingleton intersection hypothesis in the
previous theorem for two different base A-copies. -/
theorem no_common_projected_copy_of_base_aLinear
    (A : RelStructure L UA)
    (Base : RelStructure L P)
    (hLinear : ALinear A Base)
    (α₀ β₀ : RelStructure.Embedding A Base)
    (hne : ¬ SameCopy α₀ β₀)
    (B : StructuralRamsey.Partite.System L P V)
    (S : Set V)
    (D : StructuralRamsey.Partite.System L P W)
    (f : I → StructuralRamsey.Partite.Embedding (B.induce S) D)
    (hS :
      S ⊆ B.support
        ({ toFun := α₀.toFun, inj' := α₀.injective } : UA ↪ P))
    {i j : I} (hij : i ≠ j)
    (e : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Attachment.attach B S D f)
      ({ toFun := β₀.toFun, inj' := β₀.injective } : UA ↪ P))
    (hi :
      copyCarrier e.val ⊆
        copyCarrier
          (StructuralRamsey.Partite.Attachment.copyEmbedding
            B S D f i).toEmbedding)
    (hj :
      copyCarrier e.val ⊆
        copyCarrier
          (StructuralRamsey.Partite.Attachment.copyEmbedding
            B S D f j).toEmbedding)
    (a b : UA) (hab : a ≠ b) :
    False := by
  let α : UA ↪ P :=
    { toFun := α₀.toFun, inj' := α₀.injective }
  let β : UA ↪ P :=
    { toFun := β₀.toFun, inj' := β₀.injective }
  have hInter :
      (Set.range α ∩ Set.range β).Subsingleton := by
    simpa [α, β, copyCarrier] using hLinear α₀ β₀ hne
  exact
    no_common_projected_copy_of_subsingleton_base_intersection
      A B S D f α β hS hInter hij e hi hj a b hab

end StructuralRamsey.Girth

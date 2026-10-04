import Girth.AttachmentGeometry
import Girth.TreeGeometry

/-! # Strong pieces in free picture attachments

The standard picture extension is a free attachment of many copies of the old
picture to one core.  Irreducibility localizes every ambient A-copy to the core
or one attached copy.  If the gluing subsystem is A-strong in the old picture,
the core remains A-strong in the attachment.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA V W I : Type v}

/-- Every embedded irreducible copy in a free attachment factors through the
core or through one standard copy, with exactly the same image carrier. -/
theorem attachment_irreducible_copy_localize
    {A : RelStructure L UA}
    (B : RelStructure L V) (S : Set V) (D : RelStructure L W)
    (f : I → Embedding (B.induce S) D)
    (hA : A.Irreducible)
    (e : Embedding A (RelStructure.Attachment.attach B S D f)) :
    (∃ eD : Embedding A D,
        SameCopy e
          ((RelStructure.Attachment.coreEmbedding B S D f).comp eD)) ∨
      (∃ i : I, ∃ eB : Embedding A B,
        SameCopy e
          ((RelStructure.Attachment.copyEmbedding B S D f i).comp eB)) := by
  classical
  let T : Set (RelStructure.Attachment.Vertex S (W := W) (I := I)) :=
    Set.range e
  have hT :
      ((RelStructure.Attachment.attach B S D f).induce T).Irreducible :=
    hA.range_embedding e
  rcases RelStructure.Attachment.irreducible_core_or_copy
      (B := B) (S := S) (D := D) (f := f) T hT with
    hCore | ⟨i, hCopy⟩
  · let core := RelStructure.Attachment.coreEmbedding B S D f
    have hRange : ∀ a : UA, ∃ d : W, e a = core d := by
      intro a
      rcases hCore ⟨e a, ⟨a, rfl⟩⟩ with ⟨d, hd⟩
      exact ⟨d, hd⟩
    let eD : Embedding A D :=
      e.factorThroughRange core hRange
    have heD (a : UA) : e a = core (eD a) :=
      Classical.choose_spec (hRange a)
    left
    refine ⟨eD, ?_⟩
    change Set.range e = Set.range (core.comp eD)
    apply Set.Subset.antisymm
    · rintro x ⟨a, rfl⟩
      exact ⟨a, (heD a).symm⟩
    · rintro x ⟨a, rfl⟩
      exact ⟨a, heD a⟩
  · let copy := RelStructure.Attachment.copyEmbedding B S D f i
    have hRange : ∀ a : UA, ∃ b : V, e a = copy b := by
      intro a
      rcases hCopy ⟨e a, ⟨a, rfl⟩⟩ with ⟨b, hb⟩
      exact ⟨b, hb⟩
    let eB : Embedding A B :=
      e.factorThroughRange copy hRange
    have heB (a : UA) : e a = copy (eB a) :=
      Classical.choose_spec (hRange a)
    right
    refine ⟨i, eB, ?_⟩
    change Set.range e = Set.range (copy.comp eB)
    apply Set.Subset.antisymm
    · rintro x ⟨a, rfl⟩
      exact ⟨a, (heB a).symm⟩
    · rintro x ⟨a, rfl⟩
      exact ⟨a, heB a⟩

/-- If the gluing subsystem is A-strong in the old picture, then the core of
the free attachment is A-strong in the whole extension. -/
theorem attachment_core_aStrong
    {A : RelStructure L UA}
    (B : RelStructure L V) (S : Set V) (D : RelStructure L W)
    (f : I → Embedding (B.induce S) D)
    (hA : A.Irreducible)
    (hS : AStrong A B S) :
    AStrong A (RelStructure.Attachment.attach B S D f)
      (copyCarrier (RelStructure.Attachment.coreEmbedding B S D f)) := by
  classical
  let core := RelStructure.Attachment.coreEmbedding B S D f
  intro e hMeet
  rcases attachment_irreducible_copy_localize
      B S D f hA e with
    ⟨eD, heD⟩ | ⟨i, eB, heB⟩
  · intro x hx
    change copyCarrier e = copyCarrier (core.comp eD) at heD
    rw [heD] at hx
    rcases hx with ⟨a, ha⟩
    exact ⟨eD a, ha⟩
  · change copyCarrier e =
        copyCarrier
          ((RelStructure.Attachment.copyEmbedding B S D f i).comp eB)
      at heB
    have hMeet' :
        ¬ (copyCarrier
            ((RelStructure.Attachment.copyEmbedding B S D f i).comp eB) ∩
            copyCarrier core).Subsingleton := by
      simpa [heB] using hMeet
    rw [Set.not_subsingleton_iff] at hMeet'
    rcases hMeet' with ⟨x, hx, y, hy, hxy⟩
    rcases hx.1 with ⟨ax, hax⟩
    rcases hy.1 with ⟨ay, hay⟩
    rcases hx.2 with ⟨dx, hdx⟩
    rcases hy.2 with ⟨dy, hdy⟩
    have hxS : eB ax ∈ S := by
      apply RelStructure.Attachment.mem_of_copyMap_eq_inl
        (B := B) (S := S) (D := D) (f := f)
      exact hax.trans hdx.symm
    have hyS : eB ay ∈ S := by
      apply RelStructure.Attachment.mem_of_copyMap_eq_inl
        (B := B) (S := S) (D := D) (f := f)
      exact hay.trans hdy.symm
    have hxyB : eB ax ≠ eB ay := by
      intro hEq
      apply hxy
      calc
        x = RelStructure.Attachment.copyEmbedding B S D f i (eB ax) :=
          hax.symm
        _ = RelStructure.Attachment.copyEmbedding B S D f i (eB ay) :=
          congrArg
            (RelStructure.Attachment.copyEmbedding B S D f i) hEq
        _ = y := hay
    have hMeetB :
        ¬ (copyCarrier eB ∩ S).Subsingleton := by
      rw [Set.not_subsingleton_iff]
      exact ⟨eB ax, ⟨⟨ax, rfl⟩, hxS⟩,
        eB ay, ⟨⟨ay, rfl⟩, hyS⟩, hxyB⟩
    have hSub : copyCarrier eB ⊆ S :=
      hS eB hMeetB
    intro z hz
    rw [heB] at hz
    rcases hz with ⟨a, ha⟩
    have hmem : eB a ∈ S := hSub ⟨a, rfl⟩
    refine ⟨f i ⟨eB a, hmem⟩, ?_⟩
    calc
      core (f i ⟨eB a, hmem⟩) =
          RelStructure.Attachment.copyEmbedding B S D f i (eB a) :=
        (RelStructure.Attachment.copy_extends
          B S D f i ⟨eB a, hmem⟩).symm
      _ = z := ha

end StructuralRamsey.Girth

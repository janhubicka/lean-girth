import Girth.AttachmentStrongness

/-! # Strong standard copies and A-linearity of picture attachments

Once the core is strong, a standard copy can fail to be strong only through
another standard copy.  Exact copy-copy intersections force such a crossing
through the core, reducing again to core strongness.  Global A-linearity then
follows by localizing one of two intersecting A-copies to a strong piece.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA V W I : Type v}

/-- If the gluing subsystem is A-strong in the old picture and every gluing
image is A-strong in the core, then every standard copy is A-strong in the
full attachment. -/
theorem attachment_copy_aStrong
    {A : RelStructure L UA}
    (B : RelStructure L V) (S : Set V) (D : RelStructure L W)
    (f : I → Embedding (B.induce S) D)
    (hA : A.Irreducible)
    (hS : AStrong A B S)
    (hImage : ∀ i : I, AStrong A D (copyCarrier (f i)))
    (i : I) :
    AStrong A (RelStructure.Attachment.attach B S D f)
      (copyCarrier (RelStructure.Attachment.copyEmbedding B S D f i)) := by
  classical
  let core := RelStructure.Attachment.coreEmbedding B S D f
  let copyI := RelStructure.Attachment.copyEmbedding B S D f i
  have hCore : AStrong A (RelStructure.Attachment.attach B S D f)
      (copyCarrier core) :=
    attachment_core_aStrong B S D f hA hS
  intro e hMeet
  by_cases hCoreSmall :
      (copyCarrier e ∩ copyCarrier core).Subsingleton
  · rcases attachment_irreducible_copy_localize
      B S D f hA e with
      ⟨eD, heD⟩ | ⟨j, eB, heB⟩
    · exfalso
      apply hMeet
      intro x hx y hy
      apply hCoreSmall
      · constructor
        · exact hx.1
        · change copyCarrier e =
            copyCarrier (core.comp eD) at heD
          have hx' : x ∈ copyCarrier (core.comp eD) := by
            rw [← heD]
            exact hx.1
          rcases hx' with ⟨a, ha⟩
          exact ⟨eD a, ha⟩
      · constructor
        · exact hy.1
        · change copyCarrier e =
            copyCarrier (core.comp eD) at heD
          have hy' : y ∈ copyCarrier (core.comp eD) := by
            rw [← heD]
            exact hy.1
          rcases hy' with ⟨a, ha⟩
          exact ⟨eD a, ha⟩
    · by_cases hji : j = i
      · subst j
        intro z hz
        change copyCarrier e =
            copyCarrier
              ((RelStructure.Attachment.copyEmbedding B S D f i).comp eB)
          at heB
        rw [heB] at hz
        rcases hz with ⟨a, ha⟩
        exact ⟨eB a, ha⟩
      · exfalso
        have hSubCore :
            copyCarrier
                (RelStructure.Attachment.copyEmbedding B S D f j) ∩
              copyCarrier copyI ⊆
            copyCarrier core :=
          attachment_copy_copy_intersection_subset_core
            B S D f hji
        apply hMeet
        intro x hx y hy
        apply hCoreSmall
        · constructor
          · exact hx.1
          · apply hSubCore
            constructor
            · change copyCarrier e =
                copyCarrier
                  ((RelStructure.Attachment.copyEmbedding B S D f j).comp eB)
                at heB
              have hx' :
                  x ∈ copyCarrier
                    ((RelStructure.Attachment.copyEmbedding B S D f j).comp eB) := by
                rw [← heB]
                exact hx.1
              rcases hx' with ⟨a, ha⟩
              exact ⟨eB a, ha⟩
            · exact hx.2
        · constructor
          · exact hy.1
          · apply hSubCore
            constructor
            · change copyCarrier e =
                copyCarrier
                  ((RelStructure.Attachment.copyEmbedding B S D f j).comp eB)
                at heB
              have hy' :
                  y ∈ copyCarrier
                    ((RelStructure.Attachment.copyEmbedding B S D f j).comp eB) := by
                rw [← heB]
                exact hy.1
              rcases hy' with ⟨a, ha⟩
              exact ⟨eB a, ha⟩
            · exact hy.2
  · have hSubCore : copyCarrier e ⊆ copyCarrier core :=
      hCore e hCoreSmall
    have hRange : ∀ a : UA, ∃ d : W, e a = core d := by
      intro a
      rcases hSubCore ⟨a, rfl⟩ with ⟨d, hd⟩
      exact ⟨d, hd.symm⟩
    let eD : Embedding A D :=
      e.factorThroughRange core hRange
    have heD (a : UA) : e a = core (eD a) :=
      Classical.choose_spec (hRange a)
    have hMeetD :
        ¬ (copyCarrier eD ∩ copyCarrier (f i)).Subsingleton := by
      rw [Set.not_subsingleton_iff] at hMeet
      rcases hMeet with ⟨x, hx, y, hy, hxy⟩
      rcases hx.1 with ⟨ax, hax⟩
      rcases hx.2 with ⟨bx, hbx⟩
      rcases hy.1 with ⟨ay, hay⟩
      rcases hy.2 with ⟨by, hby⟩
      have hbxEq :
          RelStructure.Attachment.copyMap B S D f i bx =
            Sum.inl (eD ax) := by
        change RelStructure.Attachment.copyEmbedding B S D f i bx =
          core (eD ax)
        exact hbx.trans (hax.symm.trans (heD ax))
      have hbyEq :
          RelStructure.Attachment.copyMap B S D f i by =
            Sum.inl (eD ay) := by
        change RelStructure.Attachment.copyEmbedding B S D f i by =
          core (eD ay)
        exact hby.trans (hay.symm.trans (heD ay))
      have hbxS : bx ∈ S :=
        RelStructure.Attachment.mem_of_copyMap_eq_inl hbxEq
      have hbyS : by ∈ S :=
        RelStructure.Attachment.mem_of_copyMap_eq_inl hbyEq
      have hxFi : eD ax ∈ copyCarrier (f i) := by
        refine ⟨⟨bx, hbxS⟩, ?_⟩
        apply Sum.inl.inj
        exact
          (RelStructure.Attachment.copyMap_mem
            (B := B) (S := S) (D := D) (f := f) i bx hbxS).symm.trans
            hbxEq
      have hyFi : eD ay ∈ copyCarrier (f i) := by
        refine ⟨⟨by, hbyS⟩, ?_⟩
        apply Sum.inl.inj
        exact
          (RelStructure.Attachment.copyMap_mem
            (B := B) (S := S) (D := D) (f := f) i by hbyS).symm.trans
            hbyEq
      have hxyD : eD ax ≠ eD ay := by
        intro hEq
        apply hxy
        calc
          x = e ax := hax.symm
          _ = core (eD ax) := heD ax
          _ = core (eD ay) := congrArg core hEq
          _ = e ay := (heD ay).symm
          _ = y := hay
      rw [Set.not_subsingleton_iff]
      exact ⟨eD ax, ⟨⟨ax, rfl⟩, hxFi⟩,
        eD ay, ⟨⟨ay, rfl⟩, hyFi⟩, hxyD⟩
    have hSubD : copyCarrier eD ⊆ copyCarrier (f i) :=
      hImage i eD hMeetD
    intro z hz
    rcases hz with ⟨a, ha⟩
    rcases hSubD ⟨a, rfl⟩ with ⟨s, hs⟩
    refine ⟨s.1, ?_⟩
    calc
      RelStructure.Attachment.copyEmbedding B S D f i s.1 =
          core (f i s) :=
        RelStructure.Attachment.copy_extends B S D f i s
      _ = core (eD a) := congrArg core hs
      _ = e a := (heD a).symm
      _ = z := ha

/-- Strong core and standard copies reduce global A-linearity to the
piecewise A-linearity of the old picture and the core. -/
theorem attachment_aLinear
    {A : RelStructure L UA}
    (B : RelStructure L V) (S : Set V) (D : RelStructure L W)
    (f : I → Embedding (B.induce S) D)
    (hA : A.Irreducible)
    (hB : ALinear A B)
    (hD : ALinear A D)
    (hS : AStrong A B S)
    (hImage : ∀ i : I, AStrong A D (copyCarrier (f i))) :
    ALinear A (RelStructure.Attachment.attach B S D f) := by
  classical
  let core := RelStructure.Attachment.coreEmbedding B S D f
  have hCore : AStrong A (RelStructure.Attachment.attach B S D f)
      (copyCarrier core) :=
    attachment_core_aStrong B S D f hA hS
  have hCopies :
      ∀ i : I,
        AStrong A (RelStructure.Attachment.attach B S D f)
          (copyCarrier (RelStructure.Attachment.copyEmbedding B S D f i)) :=
    fun i => attachment_copy_aStrong B S D f hA hS hImage i
  intro e g hne
  by_contra hMeet
  rcases attachment_irreducible_copy_localize
      B S D f hA e with
    ⟨eD, heD⟩ | ⟨i, eB, heB⟩
  · have hSubE : copyCarrier e ⊆ copyCarrier core := by
      change copyCarrier e = copyCarrier (core.comp eD) at heD
      rw [heD]
      rintro x ⟨a, ha⟩
      exact ⟨eD a, ha⟩
    have hMeetCore :
        ¬ (copyCarrier g ∩ copyCarrier core).Subsingleton := by
      intro hs
      apply hMeet
      intro x hx y hy
      exact hs ⟨hx.2, hSubE hx.1⟩ ⟨hy.2, hSubE hy.1⟩
    have hSubG : copyCarrier g ⊆ copyCarrier core :=
      hCore g hMeetCore
    exact hne
      (sameCopy_of_contained_and_not_subsingleton
        hD e g core hSubE hSubG hMeet)
  · let copyI := RelStructure.Attachment.copyEmbedding B S D f i
    have hSubE : copyCarrier e ⊆ copyCarrier copyI := by
      change copyCarrier e = copyCarrier (copyI.comp eB) at heB
      rw [heB]
      rintro x ⟨a, ha⟩
      exact ⟨eB a, ha⟩
    have hMeetCopy :
        ¬ (copyCarrier g ∩ copyCarrier copyI).Subsingleton := by
      intro hs
      apply hMeet
      intro x hx y hy
      exact hs ⟨hx.2, hSubE hx.1⟩ ⟨hy.2, hSubE hy.1⟩
    have hSubG : copyCarrier g ⊆ copyCarrier copyI :=
      hCopies i g hMeetCopy
    exact hne
      (sameCopy_of_contained_and_not_subsingleton
        hB e g copyI hSubE hSubG hMeet)

end StructuralRamsey.Girth

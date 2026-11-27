import Girth.ContactFreeTree

/-! One unfolding step for a tree of traces. Full copies are glued
along their actual parent intersection; points outside the trace set
can acquire separate lifts. The map back to the ambient structure is
retained, so these separate lifts introduce no false identifications. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W X : Type v}

private theorem contact_trace_attach_interface
    {A : RelStructure L U} {B : RelStructure L V} {C : RelStructure L W}
    {T : RelStructure L X} {Q : Type v} {D : RelStructure L Q}
    (b₀ b₁ : Embedding B C) (e : Embedding B T)
    (p : X → W) (hp : T.IsHomomorphism C p) (he : ∀ x, p (e x) = b₀ x)
    (f₀ f₁ : Embedding D B)
    (hOverlap : ∀ x y, b₀ x = b₁ y ↔ ∃ d, x = f₀ d ∧ y = f₁ d)
    (hExtend : ∀ (Y : Type v) (S : RelStructure L Y)
      (i₀ : Embedding T S) (i₁ : Embedding B S),
      IsFreeAmalgam (e.comp f₀) f₁ i₀ i₁ → ContactFreeTree A B Y S) :
    ∃ (Y : Type v) (S : RelStructure L Y), ContactFreeTree A B Y S ∧
      ∃ (i₀ : Embedding T S) (i₁ : Embedding B S) (q : Y → W),
        S.IsHomomorphism C q ∧ (∀ x, q (i₀ x) = p x) ∧
        (∀ x, q (i₁ x) = b₁ x) ∧
        (∀ x y, b₀ x = b₁ y → i₀ (e x) = i₁ y) := by
  let Y := FreeAmalgam.Vertex D T B (e.comp f₀) f₁
  let S := FreeAmalgam.amalgam D T B (e.comp f₀) f₁
  let i₀ := FreeAmalgam.leftEmbedding D T B (e.comp f₀) f₁
  let i₁ := FreeAmalgam.rightEmbedding D T B (e.comp f₀) f₁
  have hfree := FreeAmalgam.isFreeAmalgam D T B (e.comp f₀) f₁
  have hc (d : Q) : p ((e.comp f₀) d) = b₁ (f₁ d) := by
    change p (e (f₀ d)) = _
    rw [he]
    exact (hOverlap _ _).mpr ⟨d,rfl,rfl⟩
  obtain ⟨q,hq,hq₀,hq₁⟩ := contact_freeAmalgam_map hfree p b₁ hp
    (fun R x hx => (b₁.map_rel_iff R x).mpr hx) hc
  refine ⟨Y,S,hExtend Y S i₀ i₁ hfree,i₀,i₁,q,hq,hq₀,hq₁,?_⟩
  intro x y hxy
  obtain ⟨d,rfl,rfl⟩ := (hOverlap x y).mp hxy
  exact (hfree.overlap _ _).mpr ⟨d,rfl,rfl⟩

theorem contact_trace_attach
    {A : RelStructure L U} {B : RelStructure L V} {C : RelStructure L W}
    {T : RelStructure L X} (hT : ContactFreeTree A B X T)
    (b₀ b₁ : Embedding B C) (hOverlap : SupportedBCopyOverlap A b₀ b₁)
    (e : Embedding B T) (p : X → W) (hp : T.IsHomomorphism C p)
    (he : ∀ x, p (e x) = b₀ x) :
    ∃ (Y : Type v) (S : RelStructure L Y), ContactFreeTree A B Y S ∧
      ∃ (i₀ : Embedding T S) (i₁ : Embedding B S) (q : Y → W),
        S.IsHomomorphism C q ∧ (∀ x, q (i₀ x) = p x) ∧
        (∀ x, q (i₁ x) = b₁ x) ∧
        (∀ x y, b₀ x = b₁ y → i₀ (e x) = i₁ y) := by
  classical
  rcases hOverlap with hEmpty | ⟨a,hA⟩ | ⟨w,hw,hs₀,hs₁⟩
  · let f₀ := ambientEmptyToMember b₀
    let f₁ := ambientEmptyToMember b₁
    apply contact_trace_attach_interface b₀ b₁ e p hp he f₀ f₁
    · intro x y
      constructor
      · intro hxy
        have hm : b₀ x ∈ copyCarrier b₀ ∩ copyCarrier b₁ :=
          ⟨⟨x,rfl⟩,⟨y,hxy.symm⟩⟩
        rw [hEmpty] at hm
        exact hm.elim
      · rintro ⟨d,_,_⟩
        exact PEmpty.elim d
    · intro Y S i₀ i₁ hfree
      exact .glueEmpty hT (e.comp f₀) f₁ i₀ i₁ hfree
  · have h₀ : copyCarrier a ⊆ copyCarrier b₀ := by
      rw [← hA]
      exact Set.inter_subset_left
    have h₁ : copyCarrier a ⊆ copyCarrier b₁ := by
      rw [← hA]
      exact Set.inter_subset_right
    let f₀ := aCopyFactorIntoMember a b₀ h₀
    let f₁ := aCopyFactorIntoMember a b₁ h₁
    apply contact_trace_attach_interface b₀ b₁ e p hp he f₀ f₁
    · intro x y
      constructor
      · intro hxy
        have hm : b₀ x ∈ copyCarrier a := by
          rw [← hA]
          exact ⟨⟨x,rfl⟩,⟨y,hxy.symm⟩⟩
        obtain ⟨d,hd⟩ := hm
        refine ⟨d,b₀.injective ?_,b₁.injective ?_⟩
        · exact hd.symm.trans (aCopyFactorIntoMember_spec a b₀ h₀ d).symm
        · exact hxy.symm.trans (hd.symm.trans (aCopyFactorIntoMember_spec a b₁ h₁ d).symm)
      · rintro ⟨d,rfl,rfl⟩
        exact (aCopyFactorIntoMember_spec a b₀ h₀ d).trans
          (aCopyFactorIntoMember_spec a b₁ h₁ d).symm
    · intro Y S i₀ i₁ hfree
      exact .glueA hT (e.comp f₀) f₁ i₀ i₁ hfree
  · obtain ⟨a₀,⟨u₀,hu₀⟩,ha₀⟩ := hs₀
    obtain ⟨a₁,⟨u₁,hu₁⟩,ha₁⟩ := hs₁
    let α₀ := aCopyFactorIntoMember a₀ b₀ ha₀
    let α₁ := aCopyFactorIntoMember a₁ b₁ ha₁
    let f₀ := ambientPointEmbedding a₀ α₀ u₀ w hu₀
    let f₁ := ambientPointEmbedding a₁ α₁ u₁ w hu₁
    have hf₀ (d : PUnit) : b₀ (f₀ d) = w :=
      (aCopyFactorIntoMember_spec a₀ b₀ ha₀ u₀).trans hu₀
    have hf₁ (d : PUnit) : b₁ (f₁ d) = w :=
      (aCopyFactorIntoMember_spec a₁ b₁ ha₁ u₁).trans hu₁
    apply contact_trace_attach_interface b₀ b₁ e p hp he f₀ f₁
    · intro x y
      constructor
      · intro hxy
        have hm : b₀ x ∈ ({w} : Set W) := by
          rw [← hw]
          exact ⟨⟨x,rfl⟩,⟨y,hxy.symm⟩⟩
        have hx : b₀ x = w := Set.mem_singleton_iff.mp hm
        exact ⟨PUnit.unit,b₀.injective (hx.trans (hf₀ _).symm),
          b₁.injective (hxy.symm.trans (hx.trans (hf₁ _).symm))⟩
      · rintro ⟨d,rfl,rfl⟩
        exact (hf₀ d).trans (hf₁ d).symm
    · intro Y S i₀ i₁ hfree
      exact .gluePoint hT (e.comp f₀) f₁
        ⟨e.comp α₀,fun _ => ⟨u₀,rfl⟩⟩ ⟨α₁,fun _ => ⟨u₁,rfl⟩⟩ i₀ i₁ hfree

end StructuralRamsey.Girth

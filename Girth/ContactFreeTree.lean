import Girth.SupportedCopyForest

/-! Auxiliary supported tree amalgams with literal empty attachments.
These retain a natural map to the original ambient structure. They embed
into the older, stronger supported-tree representation by its checked
three-copy bridge for empty attachments. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W X : Type v}

inductive ContactFreeTree (A : RelStructure L U) (B : RelStructure L V) :
    (W : Type v) → RelStructure L W → Prop
  | copy {W : Type v} {T : RelStructure L W} (h : Iso B T) : ContactFreeTree A B W T
  | glueA {W₀ W : Type v} {T₀ : RelStructure L W₀} {T : RelStructure L W}
      (h₀ : ContactFreeTree A B W₀ T₀)
      (f₀ : Embedding A T₀) (fB : Embedding A B)
      (i₀ : Embedding T₀ T) (iB : Embedding B T)
      (hfree : IsFreeAmalgam f₀ fB i₀ iB) : ContactFreeTree A B W T
  | gluePoint {W₀ W : Type v} {T₀ : RelStructure L W₀} {T : RelStructure L W}
      {D : RelStructure L PUnit} (h₀ : ContactFreeTree A B W₀ T₀)
      (f₀ : Embedding D T₀) (fB : Embedding D B)
      (support₀ : ∃ α : Embedding A T₀, ∀ d, ∃ a, f₀ d = α a)
      (supportB : ∃ α : Embedding A B, ∀ d, ∃ a, fB d = α a)
      (i₀ : Embedding T₀ T) (iB : Embedding B T)
      (hfree : IsFreeAmalgam f₀ fB i₀ iB) : ContactFreeTree A B W T
  | glueEmpty {W₀ W : Type v} {T₀ : RelStructure L W₀} {T : RelStructure L W}
      {D : RelStructure L PEmpty} (h₀ : ContactFreeTree A B W₀ T₀)
      (f₀ : Embedding D T₀) (fB : Embedding D B)
      (i₀ : Embedding T₀ T) (iB : Embedding B T)
      (hfree : IsFreeAmalgam f₀ fB i₀ iB) : ContactFreeTree A B W T

theorem ContactFreeTree.embeds_supportedTree
    {A : RelStructure L U} {B : RelStructure L V} {T : RelStructure L W}
    (hT : ContactFreeTree A B W T) (α : Embedding A B)
    (a₀ a₁ : U) (hne : a₀ ≠ a₁) :
    ∃ (X : Type v) (S : RelStructure L X) (e : Embedding T S),
      ASupportedTreeAmalgam A B X S := by
  classical
  induction hT with
  | copy h => exact ⟨_,_,(Iso.refl _).toEmbedding,.copy h⟩
  | glueA h₀ f₀ fB i₀ iB hfree ih =>
      obtain ⟨X,S,e,hS⟩ := ih
      obtain ⟨Y,R,hR,j₀,jB,hnew⟩ := hS.exists_freeGlueA (e.comp f₀) fB
      exact ⟨Y,R,freeAmalgam_liftEmbedding_sameOverlap hfree hnew e
        (Iso.refl B).toEmbedding (fun _ => rfl) (fun _ => rfl),hR⟩
  | gluePoint h₀ f₀ fB hs₀ hsB i₀ iB hfree ih =>
      obtain ⟨X,S,e,hS⟩ := ih
      have hs : ∃ β : Embedding A S, ∀ d, ∃ a, (e.comp f₀) d = β a := by
        obtain ⟨β,hβ⟩ := hs₀
        refine ⟨e.comp β,?_⟩
        intro d
        obtain ⟨a,ha⟩ := hβ d
        exact ⟨a,congrArg e ha⟩
      obtain ⟨Y,R,hR,j₀,jB,hnew⟩ := hS.exists_freeGluePoint (e.comp f₀) fB hs hsB
      exact ⟨Y,R,freeAmalgam_liftEmbedding_sameOverlap hfree hnew e
        (Iso.refl B).toEmbedding (fun _ => rfl) (fun _ => rfl),hR⟩
  | glueEmpty h₀ f₀ fB i₀ iB hfree ih =>
      obtain ⟨X,S,e,hS⟩ := ih
      obtain ⟨Y,R,hR,j₀,jB,hd,hs⟩ := hS.exists_disjointCopyExtension_split
        (Classical.choice (hS.exists_aEmbedding α)) α a₀ a₁ hne
      have hnew := inducedImageUnion_isFreeAmalgam_of_disjoint
        (e.comp f₀) fB j₀ jB hd hs
      let e' := freeAmalgam_liftEmbedding_sameOverlap hfree hnew e
        (Iso.refl B).toEmbedding (fun _ => rfl) (fun _ => rfl)
      exact ⟨Y,R,(induceToAmbient R _).comp e',hR⟩

/-- Compatible positive maps on the two sides descend through a free amalgam.
The target need not itself be a free amalgam. -/
theorem contact_freeAmalgam_map
    {D : RelStructure L U} {T : RelStructure L V} {B : RelStructure L W}
    {S : RelStructure L X} {Y : Type v} {C : RelStructure L Y}
    {f₀ : Embedding D T} {fB : Embedding D B}
    {i₀ : Embedding T S} {iB : Embedding B S}
    (hfree : IsFreeAmalgam f₀ fB i₀ iB)
    (p : V → Y) (b : W → Y) (hp : T.IsHomomorphism C p) (hb : B.IsHomomorphism C b)
    (hcompat : ∀ d, p (f₀ d) = b (fB d)) :
    ∃ q : X → Y, S.IsHomomorphism C q ∧
      (∀ x, q (i₀ x) = p x) ∧ (∀ x, q (iB x) = b x) := by
  classical
  let q (z : X) : Y := if h : ∃ x, z = i₀ x then p (Classical.choose h)
    else b (Classical.choose ((hfree.covers z).resolve_left h))
  have hleft (x : V) : q (i₀ x) = p x := by
    have h : ∃ y, i₀ x = i₀ y := ⟨x,rfl⟩
    simp only [q,dite_eq_left h]
    exact congrArg p (i₀.injective (Classical.choose_spec h).symm)
  have hright (y : W) : q (iB y) = b y := by
    by_cases h : ∃ x, iB y = i₀ x
    · obtain ⟨d,hx,hy⟩ := (hfree.overlap (Classical.choose h) y).mp
        (Classical.choose_spec h).symm
      simp only [q,dite_eq_left h]
      rw [hx,hy]
      exact hcompat d
    · simp only [q,dite_eq_right h]
      exact congrArg b (iB.injective
        (Classical.choose_spec ((hfree.covers (iB y)).resolve_left h)).symm)
  refine ⟨q,?_,hleft,hright⟩
  intro R z hz
  rcases (hfree.rel_iff R z).mp hz with ⟨x,hx,rfl⟩ | ⟨y,hy,rfl⟩
  · have he : q ∘ (i₀ ∘ x) = p ∘ x := funext (fun k => hleft (x k))
    rw [he]
    exact hp R x hx
  · have he : q ∘ (iB ∘ y) = b ∘ y := funext (fun k => hright (y k))
    rw [he]
    exact hb R y hy

end StructuralRamsey.Girth

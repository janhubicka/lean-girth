import Girth.AttachmentStrongness
import Girth.OrderCompletionSupport

set_option autoImplicit false

namespace StructuralRamsey.Girth

open RelStructure

universe u v
variable {L : RelLanguage.{u}} {U V W I X : Type v}
variable {A : RelStructure L U}

private def attachmentReductMaps
    (B : RelStructure L.withOrder V) (S : Set V)
    (D : RelStructure L.withOrder W) (f : I → Embedding (B.induce S) D) :
    I → Embedding (B.orderReduct.induce S) D.orderReduct :=
  fun i => {
    toFun := f i
    injective := (f i).injective
    map_rel_iff := fun r z => (f i).map_rel_iff (.inl r) z
  }

private theorem compare_in_embedding
    {B : RelStructure L.withOrder V} {D : RelStructure L.withOrder X}
    (g : Embedding B D) (hB : orderComparesCopies A B)
    (a : Embedding A D.orderReduct) (b : Embedding A B.orderReduct)
    (hRange : ∀ u : U, ∃ v : U, a u = g (b v))
    {x y : U} (hxy : x ≠ y) :
    D.rel (.inr ()) ![a x, a y] ∨ D.rel (.inr ()) ![a y, a x] := by
  obtain ⟨x', hx⟩ := hRange x
  obtain ⟨y', hy⟩ := hRange y
  have hxy' : x' ≠ y' := by
    rintro rfl
    exact hxy (a.injective (hx.trans hy.symm))
  have transfer (p q : V) (h : B.rel (.inr ()) ![p, q]) :
      D.rel (.inr ()) ![g p, g q] := by
    have hTuple : (g ∘ ![p, q]) = ![g p, g q] := by
      funext i
      fin_cases i <;> rfl
    have hRel : D.rel (.inr ()) (g ∘ ![p, q]) := (g.map_rel_iff (.inr ()) _).mpr h
    let orderRel : (Fin 2 → X) → Prop :=
      fun pair => D.rel (Sum.inr () : L.withOrder.Symbol) pair
    exact Eq.mp (congrArg orderRel hTuple) hRel
  rw [hx, hy]
  exact (hB b x' y' hxy').imp (transfer _ _) (transfer _ _)

/-- With the order forgotten, each irreducible source copy lies in the core or
one attached piece. Its pairs therefore retain the comparisons of that piece.
The order may remain incomplete across pieces. -/
theorem orderComparesCopies_attachment_of_irreducible
    (B : RelStructure L.withOrder V) (S : Set V)
    (D : RelStructure L.withOrder W) (f : I → Embedding (B.induce S) D)
    (hA : A.Irreducible) (hB : orderComparesCopies A B)
    (hD : orderComparesCopies A D) :
    orderComparesCopies A (Attachment.attach B S D f) := by
  intro a x y hxy
  let f₀ := attachmentReductMaps B S D f
  let a₀ : Embedding A (Attachment.attach B.orderReduct S D.orderReduct f₀) := a
  rcases attachment_irreducible_copy_localize B.orderReduct S D.orderReduct f₀ hA a₀ with
    ⟨b, h⟩ | ⟨i, b, h⟩
  · apply compare_in_embedding (Attachment.coreEmbedding B S D f) hD a b _ hxy
    intro u
    have hu : a₀ u ∈ copyCarrier
        ((Attachment.coreEmbedding B.orderReduct S D.orderReduct f₀).comp b) := by
      rw [← h]
      exact ⟨u, rfl⟩
    obtain ⟨z, hz⟩ := hu
    exact ⟨z, hz.symm⟩
  · apply compare_in_embedding (Attachment.copyEmbedding B S D f i) hB a b _ hxy
    intro u
    have hu : a₀ u ∈ copyCarrier
        ((Attachment.copyEmbedding B.orderReduct S D.orderReduct f₀ i).comp b) := by
      rw [← h]
      exact ⟨u, rfl⟩
    obtain ⟨z, hz⟩ := hu
    exact ⟨z, hz.symm⟩

end StructuralRamsey.Girth

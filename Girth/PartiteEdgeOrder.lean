import Girth.OrderCompletionSupport
import PartiteConstruction.Partite.Operations

set_option autoImplicit false

namespace StructuralRamsey.Partite

open StructuralRamsey.Girth

universe u v
variable {L : RelLanguage.{u}} {U P X Y : Type v} [LinearOrder P]

private def shareCopy (A : RelStructure L U) (C : RelStructure L X) (x y : X) : Prop :=
  ∃ a : RelStructure.Embedding A C, x ∈ copyCarrier a ∧ y ∈ copyCarrier a

/-- Record the fine-part order on pairs in a common source copy. The order
inside each fine part is handled separately. -/
def System.edgeOrder (H : System L P X) (A : RelStructure L U) :
    System L.withOrder P X where
  toRelStructure := {
    rel R := by
      cases R with
      | inl r => exact H.rel r
      | inr _ =>
          exact fun z : Fin 2 → X =>
            H.part (z 0) < H.part (z 1) ∧ shareCopy A H.toRelStructure (z 0) (z 1)
  }
  part := H.part
  transversal := by
    intro R z hz i j hpart
    cases R with
    | inl r => exact H.transversal r z hz i j hpart
    | inr r =>
        change Fin 2 → X at z
        change H.part (z 0) < H.part (z 1) ∧ _ at hz
        change H.part (z i) = H.part (z j) at hpart
        fin_cases i <;> fin_cases j
        · rfl
        · exact False.elim ((ne_of_lt hz.1) hpart)
        · exact False.elim ((ne_of_lt hz.1) hpart.symm)
        · rfl

/-- When the copies meet each fine part at most once, the recorded
comparisons give a complete order on each copy in the edge reduct. -/
theorem System.edgeOrder_comparesCopies (H : System L P X) (A : RelStructure L U)
    (hFine : ∀ a : RelStructure.Embedding A H.toRelStructure,
      Function.Injective (H.part ∘ a)) :
    orderComparesCopies A (H.edgeOrder A).toRelStructure := by
  intro a x y hxy
  let a₀ : RelStructure.Embedding A H.toRelStructure := a
  rcases lt_or_gt_of_ne (fun h => hxy (hFine a₀ h)) with h | h
  · exact Or.inl ⟨h, a₀, ⟨x, rfl⟩, ⟨y, rfl⟩⟩
  · exact Or.inr ⟨h, a₀, ⟨y, rfl⟩, ⟨x, rfl⟩⟩

/-- A strong part-preserving embedding also preserves and reflects the
edge comparisons. For reflection a copy containing the two image vertices
lies entirely in the image, and so factors through the embedding. -/
noncomputable def Embedding.edgeOrder
    {H : System L P X} {K : System L P Y} (f : Embedding H K)
    (A : RelStructure L U) (hStrong : AStrong A K.toRelStructure (Set.range f)) :
    Embedding (H.edgeOrder A) (K.edgeOrder A) where
  toEmbedding := {
    toFun := f
    injective := f.toEmbedding.injective
    map_rel_iff := by
      intro R z
      cases R with
      | inl r => exact f.toEmbedding.map_rel_iff r z
      | inr r =>
          change Fin 2 → X at z
          let x := z 0
          let y := z 1
          change (K.part (f x) < K.part (f y) ∧ shareCopy A K.toRelStructure (f x) (f y)) ↔
            (H.part x < H.part y ∧ shareCopy A H.toRelStructure x y)
          rw [f.map_part, f.map_part]
          constructor
          · rintro ⟨hxy, a, hx, hy⟩
            have hne : f x ≠ f y := fun h =>
              (ne_of_lt hxy) (congrArg H.part (f.toEmbedding.injective h))
            have hsub : copyCarrier a ⊆ Set.range f := hStrong a
              (fun h => hne (h ⟨hx, x, rfl⟩ ⟨hy, y, rfl⟩))
            have hRange (p : U) : ∃ q : X, a p = f q := by
              obtain ⟨q, hq⟩ := hsub ⟨p, rfl⟩
              exact ⟨q, hq.symm⟩
            let a₀ : RelStructure.Embedding A H.toRelStructure :=
              a.factorThroughRange f.toEmbedding hRange
            have he (p : U) : a p = f (a₀ p) := Classical.choose_spec (hRange p)
            refine ⟨hxy, a₀, ?_, ?_⟩
            · obtain ⟨p, hp⟩ := hx
              exact ⟨p, f.toEmbedding.injective ((he p).symm.trans hp)⟩
            · obtain ⟨p, hp⟩ := hy
              exact ⟨p, f.toEmbedding.injective ((he p).symm.trans hp)⟩
          · rintro ⟨hxy, a, ⟨p, hp⟩, ⟨q, hq⟩⟩
            exact ⟨hxy, f.toEmbedding.comp a, ⟨p, congrArg f hp⟩, ⟨q, congrArg f hq⟩⟩
  }
  map_part := f.map_part

end StructuralRamsey.Partite

import Girth.TrainFillingLocalPrivateChoices
import Girth.TrainFillingIndexedParentwiseRealization

set_option autoImplicit false

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {A C V P X Y E I Q RQ : Type v}

namespace ParentwiseRealization

variable {W : C → PrivateWagonInput V P X} {parent : P → Q}
variable {D : OrderOneData Y E I RQ} (F : ParentwiseRealization W parent D)

/-- The literal original target vertex map used by the scattered family. -/
def targetVertexEmbedding (i : I × C) : V ↪ Y where
  toFun := fun v => F.vertex i.1 (tagVertex W i.2 (Sum.inl v))
  inj' := fun _ _ h => Sum.inl.inj
    (tagVertex_injective W i.2 ((F.vertex i.1).injective h))

theorem targetVertexEmbedding_range (i : I × C) :
    Set.range (F.targetVertexEmbedding i) = F.targetCarrier i := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨tagVertex W i.2 (Sum.inl x), ⟨Sum.inl x, ⟨x, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

/-- The selected edge family is exactly the physical edges contained in
its target carrier, once the two-point strongness test is known. -/
theorem targetEdges_eq_contained (i : I × C)
    (hPair : ∀ e : E, ∃ x y, x ≠ y ∧ x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier e)
    (hStrong : ∀ (e : E) (x y : Y), x ≠ y →
      x ∈ D.edgeCarrier e → y ∈ D.edgeCarrier e →
      x ∈ F.targetCarrier i → y ∈ F.targetCarrier i → e ∈ F.targetEdges i) :
    F.targetEdges i = {e | D.edgeCarrier e ⊆ F.targetCarrier i} := by
  ext e
  constructor
  · rintro ⟨a, ha, rfl⟩
    change D.edgeCarrier (F.edge i.1 a) ⊆ F.targetCarrier i
    rw [F.edgeCarrier_eq]
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, target_edge_carrier_subset W i.2 a ha hx, rfl⟩
  · intro he
    obtain ⟨x, y, hne, hxe, hye⟩ := hPair e
    exact hStrong e x y hne hxe hye (he hxe) (he hye)

end ParentwiseRealization

section OriginalEdges

variable
  (small : RelStructure L A) (B : RelStructure L V) (R : RelStructure L X)
  (carrier : P → Set V)
  (localCopy : ∀ c : C, ∀ p : P, Embedding (B.induce (carrier p)) R)
  (hStrong : ∀ c p, AStrong small R (copyCarrier (localCopy c p)))
  (hCover : ∀ p : P, ∀ x : {v : V // v ∈ carrier p},
    ∃ a : Embedding small (B.induce (carrier p)), x ∈ copyCarrier a)

private noncomputable abbrev localChoices (c : C) : PrivateWagonInput V P X :=
  privateChoiceOfLocalCopies small B R carrier (localCopy c) (hStrong c) hCover

local notation "W" => localChoices small B R carrier localCopy hStrong hCover
variable {parent : P → Q} {D : OrderOneData Y E I RQ}

/-- Physical edge carriers selected by scattering are images of genuine
original target edges, including their complete vertex sets. -/
theorem parentwise_targetEdge_original (F : ParentwiseRealization W parent D) (i : I × C) (e : E)
    (he : e ∈ F.targetEdges i) :
    ∃ a : Embedding small B, D.edgeCarrier e =
      F.targetVertexEmbedding i '' copyCarrier a := by
  obtain ⟨s, hs, rfl⟩ := he
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨a, ha⟩ := privateChoice_targetEdge_relational small B R carrier
    (localCopy i.2) (hStrong i.2) hCover t ht
  rw [← ha]
  refine ⟨(inclusion B (carrier t.1)).comp a, ?_⟩
  rw [F.edgeCarrier_eq]
  change F.vertex i.1 '' (tagVertex W i.2 '' (W i.2).edgeCarrier
      (privateChoice_localEdge small B R carrier (localCopy i.2) (hStrong i.2) hCover t.1 a)) = _
  rw [privateChoice_localEdge_carrier]
  simp only [Set.image_image] <;> rfl

/-- Every original target edge has its real selected physical image,
with its original first-wagon owner retained. -/
theorem parentwise_originalEdge_target [Nontrivial A]
    (F : ParentwiseRealization W parent D)
    (owner : {e : Set V // e ∈ supportCopies small B} → P)
    (hOwner : ∀ e, e.1 ⊆ carrier (owner e))
    (hLinear : ∀ p q : P, p ≠ q → (carrier p ∩ carrier q).Subsingleton)
    (i : I × C) (a : Embedding small B) :
    ∃ t : (W i.2).Edge,
      t.1 = owner ⟨copyCarrier a, ⟨a, rfl⟩⟩ ∧
      F.edge i.1 (tagEdge W i.2 t) ∈ F.targetEdges i ∧
      D.edgeCarrier (F.edge i.1 (tagEdge W i.2 t)) =
        F.targetVertexEmbedding i '' copyCarrier a := by
  obtain ⟨t, hOwnerEq, ht, hCarrier⟩ := privateChoice_originalEdge_relational small B R carrier
    (localCopy i.2) (hStrong i.2) hCover owner hOwner hLinear a
  refine ⟨t, hOwnerEq, ⟨tagEdge W i.2 t, ⟨t, ht, rfl⟩, rfl⟩, ?_⟩
  rw [F.edgeCarrier_eq]
  change F.vertex i.1 '' (tagVertex W i.2 '' (W i.2).edgeCarrier t) = _
  rw [hCarrier]
  simp only [Set.image_image] <;> rfl

end OriginalEdges
end StructuralRamsey.Girth.IndexedPrivateChoice

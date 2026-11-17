import Girth.TrainFillingIndexedSelectedPhysicalMap
import Girth.TrainFillingIndexedCarrierGeometry
import Girth.TrainFillingOrderedCanonicalPlacement

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u u' v

variable {L : RelLanguage.{u}} {K : RelLanguage.{u'}}
variable {U A C P V X Y : Type v} [LinearOrder U]
variable {old : RelStructure L U} {N : RelStructure L.withOrder Y}

/-- Fill each actual old edge of the shorter target using its unique
ordered embedding. The inserted local edges may use a different language. -/
noncomputable def UniformFillingData.ofOrderedSupportCopies
    (small : RelStructure K A) [Nontrivial A] (R : RelStructure K X)
    (enumerate : X ≃ U)
    (hLinear : ∀ e f : {s : Set Y // s ∈ supportCopies old.ordered N},
      e ≠ f → (e.1 ∩ f.1).Subsingleton)
    (hCover : ∀ x : X, ∃ a : Embedding small R, x ∈ copyCarrier a) :
    UniformFillingData Y X :=
  UniformFillingData.ofSupportCopies small R (supportCopies old.ordered N)
    (orderedFillingPlacement enumerate) (orderedFillingPlacement_range enumerate)
    hLinear hCover

namespace IndexedPrivateChoice

/-- The source embedding carries exactly its tagged first wagon. -/
theorem orderedSource_copyCarrier_eq
    (W : C → PrivateWagonInput V P X)
    (enumerate : X ≃ U) (M : RelStructure L.withOrder (Vertex W))
    (source : (C × P) → Embedding old.ordered M)
    (hSource : ∀ c : C, ∀ p : P, ∀ x : X,
      source (c, p) (enumerate x) = tagVertex W c ((W c).place p x))
    (cp : C × P) :
    copyCarrier (source cp) = contractedCarrier W cp := by
  obtain ⟨c, p⟩ := cp
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨x, rfl⟩ := enumerate.surjective u
    rw [hSource c p x]
    exact ⟨_, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
    exact ⟨enumerate x, hSource c p x⟩

/-- A selected relational copy itself determines the entire contracted edge
map. The only injectivity used is injectivity of the original carriers and
of the selected vertex embedding. -/
noncomputable def selectedOrderedOldEdgeEmbedding
    [Nontrivial X]
    (W : C → PrivateWagonInput V P X)
    (small : RelStructure K A) [Nontrivial A] (R : RelStructure K X)
    (enumerate : X ≃ U)
    (hLinear : ∀ e f : {s : Set Y // s ∈ supportCopies old.ordered N},
      e ≠ f → (e.1 ∩ f.1).Subsingleton)
    (hCover : ∀ x : X, ∃ a : Embedding small R, x ∈ copyCarrier a)
    (hFirstLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((W c).oldCarrier p ∩ (W c).oldCarrier q).Subsingleton)
    (M : RelStructure L.withOrder (Vertex W))
    (source : (C × P) → Embedding old.ordered M)
    (hSource : ∀ c : C, ∀ p : P, ∀ x : X,
      source (c, p) (enumerate x) = tagVertex W c ((W c).place p x))
    (selected : Embedding M N) :
    (C × P) ↪ (UniformFillingData.ofOrderedSupportCopies small R enumerate hLinear hCover).OldEdge := by
  let H := UniformFillingData.ofOrderedSupportCopies small R enumerate hLinear hCover
  refine H.oldEdgeEmbedding_of_exact_carriers (contractedCarrier W)
    (contractedCarrier_injective W hFirstLinear) selected.toFunctionEmbedding
    (fun cp => ⟨copyCarrier (selected.comp (source cp)), ⟨_, rfl⟩⟩) ?_
  intro cp
  rw [← orderedSource_copyCarrier_eq W enumerate M source hSource cp]
  exact (UniformPrivateTemplate.image_copyCarrier_comp
    old.ordered M N selected (source cp)).symm

/-- A contained old edge factors through the selected induced copy, and
its source carrier is one of the complete tagged first wagons. -/
theorem selectedOrderedOldEdgeEmbedding_range
    [Nontrivial X]
    (W : C → PrivateWagonInput V P X)
    (small : RelStructure K A) [Nontrivial A] (R : RelStructure K X)
    (enumerate : X ≃ U)
    (hLinear : ∀ e f : {s : Set Y // s ∈ supportCopies old.ordered N},
      e ≠ f → (e.1 ∩ f.1).Subsingleton)
    (hCover : ∀ x : X, ∃ a : Embedding small R, x ∈ copyCarrier a)
    (hFirstLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((W c).oldCarrier p ∩ (W c).oldCarrier q).Subsingleton)
    (M : RelStructure L.withOrder (Vertex W))
    (source : (C × P) → Embedding old.ordered M)
    (hSource : ∀ c : C, ∀ p : P, ∀ x : X,
      source (c, p) (enumerate x) = tagVertex W c ((W c).place p x))
    (hSupport : supportCopies old.ordered M = Set.range (contractedCarrier W))
    (selected : Embedding M N) :
    Set.range (selectedOrderedOldEdgeEmbedding W small R enumerate
      hLinear hCover hFirstLinear M source hSource selected) =
      {e | e.1 ⊆ copyCarrier selected} := by
  ext e
  constructor
  · rintro ⟨cp, rfl⟩
    change copyCarrier (selected.comp (source cp)) ⊆ copyCarrier selected
    rintro _ ⟨u, rfl⟩
    exact ⟨source cp u, rfl⟩
  · intro he
    change e.1 ⊆ copyCarrier selected at he
    obtain ⟨a, ha⟩ : e.1 ∈ supportCopies old.ordered N := e.2
    have hFactor : ∀ u : U, ∃ z : Vertex W, a u = selected z := by
      intro u
      have hu : a u ∈ e.1 := ha ▸ ⟨u, rfl⟩
      obtain ⟨z, hz⟩ := he hu
      exact ⟨z, hz.symm⟩
    let q : Embedding old.ordered M := a.factorThroughRange selected hFactor
    have hComp : selected.comp q = a := by
      apply Embedding.ext
      intro u
      exact (Classical.choose_spec (hFactor u)).symm
    have hq : copyCarrier q ∈ Set.range (contractedCarrier W) := by
      rw [← hSupport]
      exact ⟨q, rfl⟩
    obtain ⟨cp, hcp⟩ := hq
    refine ⟨cp, Subtype.ext ?_⟩
    change copyCarrier (selected.comp (source cp)) = e.1
    rw [← UniformPrivateTemplate.image_copyCarrier_comp old.ordered M N selected (source cp),
      orderedSource_copyCarrier_eq W enumerate M source hSource cp, hcp,
      UniformPrivateTemplate.image_copyCarrier_comp old.ordered M N selected q, hComp, ha]

/-- An actual ordered selected copy of the shortened target transports
every filled edge carrier pointwise. The equality follows from rigidity
on each old edge, even if the ambient shorter order is only partial. -/
theorem selectedOrderedFilling_edgeCarrier
    [Finite U]
    (W : C → PrivateWagonInput V P X)
    (small : RelStructure K A) [Nontrivial A] (R : RelStructure K X)
    (enumerate : X ≃ U)
    (hLinear : ∀ e f : {s : Set Y // s ∈ supportCopies old.ordered N},
      e ≠ f → (e.1 ∩ f.1).Subsingleton)
    (hCover : ∀ x : X, ∃ a : Embedding small R, x ∈ copyCarrier a)
    (hTemplate : ∀ c : C, (W c).templateEdges = supportCopies small R)
    (M : RelStructure L.withOrder (Vertex W))
    (source : (C × P) → Embedding old.ordered M)
    (hSource : ∀ c : C, ∀ p : P, ∀ x : X,
      source (c, p) (enumerate x) = tagVertex W c ((W c).place p x))
    (selected : Embedding M N)
    (β : (C × P) ↪
      (UniformFillingData.ofOrderedSupportCopies small R enumerate hLinear hCover).OldEdge)
    (hβ : ∀ c : C, ∀ p : P, (β (c, p)).1 = copyCarrier (selected.comp (source (c, p))))
    (a : Edge W) :
    let H := UniformFillingData.ofOrderedSupportCopies small R enumerate hLinear hCover
    (selectedIndexedFilledEdgeEmbedding W H hTemplate β a).1 =
      selected.toFunctionEmbedding '' edgeCarrier W a := by
  let H := UniformFillingData.ofOrderedSupportCopies small R enumerate hLinear hCover
  apply selectedIndexedFilledEdgeEmbedding_carrier W H hTemplate β selected.toFunctionEmbedding
  intro c p x
  change orderedFillingPlacement enumerate (β (c, p)) x =
    selected (tagVertex W c ((W c).place p x))
  rw [orderedFillingPlacement_comp enumerate (source (c, p)) selected
    (β (c, p)) (hβ c p) x, hSource c p x]

end IndexedPrivateChoice
end StructuralRamsey.Girth

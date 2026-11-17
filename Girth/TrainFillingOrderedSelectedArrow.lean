import Girth.TrainFillingIndexedSelectedColourWord
import Girth.TrainFillingOrderedSelectedCarriers

set_option autoImplicit false

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u u' v w

variable {L : RelLanguage.{u}} {K : RelLanguage.{u'}}
variable {U A C P V X Y I : Type v} {κ : Type w}
variable [LinearOrder U] [Finite U] [Nontrivial X] [Nonempty (C × P)]
variable {old : RelStructure L U} {N : RelStructure L.withOrder Y}

/-- The shorter ordered Ramsey arrow and the template arrow select one
component of an actual selected relational copy. Its filled edge map both
preserves carriers and gives the required monochromatic target edges. -/
theorem selectedOrderedTargetEdges_ramsey
    (W : C → PrivateWagonInput V P X)
    (small : RelStructure K A) [Nontrivial A] (R : RelStructure K X)
    (enumerate : X ≃ U)
    (hLinear : ∀ e f : {s : Set Y // s ∈ supportCopies old.ordered N},
      e ≠ f → (e.1 ∩ f.1).Subsingleton)
    (hCover : ∀ x : X, ∃ a : Embedding small R, x ∈ copyCarrier a)
    (hTemplate : ∀ c : C, (W c).templateEdges = supportCopies small R)
    (hFirstLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((W c).oldCarrier p ∩ (W c).oldCarrier q).Subsingleton)
    (M : RelStructure L.withOrder (Vertex W))
    (source : (C × P) → Embedding old.ordered M)
    (hSource : ∀ c : C, ∀ p : P, ∀ x : X,
      source (c, p) (enumerate x) = tagVertex W c ((W c).place p x))
    (selected : I → Embedding M N)
    (hShortArrow : ∀ colours : Embedding old.ordered N →
        {e : Set X // e ∈ supportCopies small R} → κ,
      ∃ i : I, ∀ a d : Embedding old.ordered M,
        colours ((selected i).comp a) = colours ((selected i).comp d))
    (hLocalArrow : ∀ word : {e : Set X // e ∈ supportCopies small R} → κ,
      ∃ (c : C) (colour : κ), ∀ p : P, ∀ e,
        e ∈ selectedCommonEdges W (supportCopies small R) hTemplate c p → word e = colour) :
    let H := UniformFillingData.ofOrderedSupportCopies small R enumerate hLinear hCover
    ∀ χ : H.toTrainFilling.NewEdge → κ,
      ∃ (i : I) (c : C) (colour : κ),
        let β := selectedOrderedOldEdgeEmbedding W small R enumerate hLinear hCover
          hFirstLinear M source hSource (selected i)
        (∀ a : Edge W, (selectedIndexedFilledEdgeEmbedding W H hTemplate β a).1 =
          (selected i).toFunctionEmbedding '' edgeCarrier W a) ∧
        (∀ e ∈ selectedIndexedFilledEdgeEmbedding W H hTemplate β '' targetEdges W c,
          χ e = colour) := by
  intro H χ
  let liftWord (e : Embedding old.ordered N) : H.TemplateEdge → κ :=
    H.colourWord χ ⟨copyCarrier e, ⟨e, rfl⟩⟩
  obtain ⟨i, hConst⟩ := hShortArrow liftWord
  let b := selected i
  let β := selectedOrderedOldEdgeEmbedding W small R enumerate hLinear hCover
    hFirstLinear M source hSource b
  obtain ⟨cp⟩ := (inferInstance : Nonempty (C × P))
  let word := liftWord (b.comp (source cp))
  obtain ⟨c, colour, hLocal⟩ := hLocalArrow word
  refine ⟨i, c, colour, ?_, ?_⟩
  · intro a
    exact selectedOrderedFilling_edgeCarrier W small R enumerate hLinear hCover hTemplate
      M source hSource b β (fun _ _ => rfl) a
  · rintro e ⟨a, ha, rfl⟩
    exact selectedIndexedTargetEdges_colourWord_constant W H hTemplate β χ word c colour
      (fun p => hConst (source (c, p)) (source cp)) hLocal a ha

end StructuralRamsey.Girth.IndexedPrivateChoice

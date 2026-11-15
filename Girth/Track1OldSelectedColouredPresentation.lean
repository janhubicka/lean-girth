import Girth.Track1ControlledPhysicalIntersection
import Girth.TrainFillingColouredOrderedEdgePresentation

/-!
# Track 1: selected EHN B embeddings reflect the WHOLE coloured edge presentation

The original functional EHN selected family is a family of full
relational B embeddings into the A-linear witness.  Retain only
A-support edges that appear inside selected target images.

Even though the EHN witness may contain other ambient relations,
every selected B image is a full INDUCED embedding of the resulting
coloured ordered edge structure, provided:
(1) the old global EHN order is monotone on selected B;
(2) the unary colour predicate is transported correctly.

For the crucial *negative* edge direction, any selected support
A-copy whose carrier is contained in an old selected B image factors
back to a genuine source A-copy. No separate strongness or
induced-output premise is assumed for this step.

STAGED DRAFT, not compiled yet.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB V I Choice : Type v}

/-- A genuine selected full B embedding into an EHN witness induces a
full embedding of the exact *positive selected-edge* presentation,
including the unary colour and within-colour order relations. -/
noncomputable def track1_oldSelectedColouredOrderedEmbedding
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    [LinearOrder VB] [LinearOrder V]
    (family : Choice → Embedding B C)
    (k : ℕ) (sourceColour : VB → I) (predicate : V → I)
    (c : Choice)
    (hMono : StrictMono (family c))
    (hPredicate : ∀ w : VB,
      predicate (family c w) = sourceColour w) :
    Embedding
      (colouredOrderedEdgeTarget k (supportCopies A B) sourceColour)
      (colouredOrderedEdgeTarget k (selectedSupportEdges A family) predicate) := by
  classical
  let b := family c
  have hImage (t : Fin k → VB) :
      b '' Set.range t = Set.range (b ∘ t) := by
    ext z
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨t i, ⟨i, rfl⟩, rfl⟩
  refine {
    toFun := b
    injective := b.injective
    map_rel_iff := ?_
  }
  intro R x
  cases R with
  | inl relation =>
      cases relation with
      | inl _ =>
          change
            (Function.Injective (b ∘ x) ∧
              Set.range (b ∘ x) ∈ selectedSupportEdges A family) ↔
            (Function.Injective x ∧
              Set.range x ∈ supportCopies A B)
          constructor
          · rintro ⟨hinj, d, a, hd⟩
            have hx : Function.Injective x := by
              intro i j hij
              exact hinj (congrArg b hij)
            let aOld : Embedding A C := (family d).comp a
            have hSub : copyCarrier aOld ⊆ copyCarrier b := by
              intro z hz
              have hzRange : z ∈ Set.range (b ∘ x) := by
                rw [hd]
                exact hz
              obtain ⟨i, hi⟩ := hzRange
              exact ⟨x i, hi⟩
            obtain ⟨aB, hCarrier⟩ :=
              track1_aEmbedding_factor_of_carrier_subset b aOld hSub
            have hImageEq : b '' Set.range x = b '' copyCarrier aB := by
              calc
                b '' Set.range x = Set.range (b ∘ x) := hImage x
                _ = copyCarrier aOld := hd
                _ = copyCarrier (b.comp aB) := hCarrier
                _ = b '' copyCarrier aB :=
                  copyCarrier_comp_eq_image b aB
            have hSourceEdge : Set.range x ∈ supportCopies A B := by
              refine ⟨aB, ?_⟩
              exact (Set.image_injective.mpr b.injective) hImageEq
            exact ⟨hx, hSourceEdge⟩
          · rintro ⟨hx, ⟨aB, haB⟩⟩
            have hEdge : Set.range (b ∘ x) ∈
                selectedSupportEdges A family := by
              refine ⟨c, aB, ?_⟩
              calc
                Set.range (b ∘ x) = b '' Set.range x := (hImage x).symm
                _ = b '' copyCarrier aB := by rw [haB]
                _ = copyCarrier (b.comp aB) :=
                  (copyCarrier_comp_eq_image b aB).symm
            exact ⟨b.injective.comp hx, hEdge⟩
      | inr colour =>
          change predicate (b (x 0)) = colour ↔
            sourceColour (x 0) = colour
          rw [hPredicate]
  | inr _ =>
      change
        (predicate (b (x 0)) = predicate (b (x 1)) ∧
          b (x 0) < b (x 1)) ↔
        (sourceColour (x 0) = sourceColour (x 1) ∧
          x 0 < x 1)
      rw [hPredicate (x 0), hPredicate (x 1)]
      exact and_congr Iff.rfl hMono.lt_iff_lt

#print axioms StructuralRamsey.Girth.track1_oldSelectedColouredOrderedEmbedding

end StructuralRamsey.Girth

import Girth.Track1SelectedActualOwnerCopies
import Girth.Track1FullSelectedSupportPieces
import Girth.Support

/-!
# Track 1: EHN full common A-edges are genuine source edges in BOTH B copies

The functional EHN class controls the intersection of two distinct
selected B image carriers: small, or exactly the carrier of a true
ambient A embedding. In the latter case this A embedding factors
through each selected B embedding, so it is an actual A-support edge
in both source copies. Both physical owner-split edge maps therefore
return the SAME old ambient A-edge.

No independent "common selected edge" hypothesis is added. This is
the final geometric adapter needed by the checked
ColouredOwnerSelectedCopy.lifted_intersection_eq_splitEdge.

STAGED DRAFT — not Lean kernel checked.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB V I Choice : Type v}

/-- Factor any full ambient A embedding whose carrier lies inside a
genuine selected B image into an actual source A embedding. -/
theorem track1_aEmbedding_factor_of_carrier_subset
    {A : RelStructure L UA} {B : RelStructure L VB}
    {C : RelStructure L V}
    (b : Embedding B C) (a : Embedding A C)
    (hSub : copyCarrier a ⊆ copyCarrier b) :
    ∃ aB : Embedding A B,
      copyCarrier a = copyCarrier (b.comp aB) := by
  classical
  have hFactor : ∀ u : UA, ∃ x : VB, a u = b x := by
    intro u
    obtain ⟨x, hx⟩ := hSub ⟨u, rfl⟩
    exact ⟨x, hx.symm⟩
  let aB : Embedding A B := a.factorThroughRange b hFactor
  have hEq : a = b.comp aB := by
    apply Embedding.ext
    intro u
    exact Classical.choose_spec (hFactor u)
  exact ⟨aB, congrArg copyCarrier hEq⟩

/-- A genuine EHN common A-copy yields the SAME physical old edge
in both selected target source-edge sets. -/
theorem track1_commonA_is_selectedSourceEdge_both
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C)
    (predicate : V → I) (allowed : Set I)
    (i j : Choice)
    (a : Embedding A C)
    (hInter :
      copyCarrier (family i) ∩ copyCarrier (family j) =
        copyCarrier a) :
    ∃ f : (selectedSupportOwnerSystem A family predicate allowed).OldEdge,
      (copyCarrier (family i) ∩ copyCarrier (family j) ⊆ f.1) ∧
      (∃ e : {e : Set VB // e ∈ supportCopies A B},
        (family i).toFunctionEmbedding '' e.1 = f.1) ∧
      (∃ e : {e : Set VB // e ∈ supportCopies A B},
        (family j).toFunctionEmbedding '' e.1 = f.1) := by
  classical
  have hSubI : copyCarrier a ⊆ copyCarrier (family i) := by
    rw [← hInter]
    exact Set.inter_subset_left
  have hSubJ : copyCarrier a ⊆ copyCarrier (family j) := by
    rw [← hInter]
    exact Set.inter_subset_right
  obtain ⟨ai, hai⟩ :=
    track1_aEmbedding_factor_of_carrier_subset (family i) a hSubI
  obtain ⟨aj, haj⟩ :=
    track1_aEmbedding_factor_of_carrier_subset (family j) a hSubJ
  let f : (selectedSupportOwnerSystem A family predicate allowed).OldEdge :=
    ⟨copyCarrier a, ⟨i, ai, hai⟩⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [hInter]
  · let e : {e : Set VB // e ∈ supportCopies A B} :=
      ⟨copyCarrier ai, ⟨ai, rfl⟩⟩
    refine ⟨e, ?_⟩
    change (family i).toFunctionEmbedding '' copyCarrier ai =
      copyCarrier a
    calc
      (family i).toFunctionEmbedding '' copyCarrier ai =
          copyCarrier ((family i).comp ai) :=
        (copyCarrier_comp_eq_image (family i) ai).symm
      _ = copyCarrier a := hai.symm
  · let e : {e : Set VB // e ∈ supportCopies A B} :=
      ⟨copyCarrier aj, ⟨aj, rfl⟩⟩
    refine ⟨e, ?_⟩
    change (family j).toFunctionEmbedding '' copyCarrier aj =
      copyCarrier a
    calc
      (family j).toFunctionEmbedding '' copyCarrier aj =
          copyCarrier ((family j).comp aj) :=
        (copyCarrier_comp_eq_image (family j) aj).symm
      _ = copyCarrier a := haj.symm

/-- Combine the actual EHN controlled-intersection conclusion with
the physical edge ownership proved above. The output is precisely
the small/whole-common-edge hypothesis of selectedLiftSupport_allowed,
not a weaker containment in an arbitrary ambient edge. -/
theorem track1_controlled_selectedPhysicalIntersections
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C)
    (predicate : V → I) (allowed : Set I)
    (hControlled : ∀ i j : Choice,
      ¬ SameCopy (family i) (family j) →
      (copyCarrier (family i) ∩ copyCarrier (family j)).Subsingleton ∨
        ∃ a : Embedding A C,
          copyCarrier (family i) ∩ copyCarrier (family j) =
            copyCarrier a)
    (i j : Choice)
    (hne : ¬ SameCopy (family i) (family j)) :
    (copyCarrier (family i) ∩ copyCarrier (family j)).Subsingleton ∨
      ∃ f : (selectedSupportOwnerSystem A family predicate allowed).OldEdge,
        copyCarrier (family i) ∩ copyCarrier (family j) ⊆ f.1 ∧
        (∃ e : {e : Set VB // e ∈ supportCopies A B},
          (family i).toFunctionEmbedding '' e.1 = f.1) ∧
        (∃ e : {e : Set VB // e ∈ supportCopies A B},
          (family j).toFunctionEmbedding '' e.1 = f.1) := by
  rcases hControlled i j hne with hSmall | ⟨a, hInter⟩
  · exact Or.inl hSmall
  · exact Or.inr
      (track1_commonA_is_selectedSourceEdge_both
        A family predicate allowed i j a hInter)

#print axioms StructuralRamsey.Girth.track1_aEmbedding_factor_of_carrier_subset
#print axioms StructuralRamsey.Girth.track1_commonA_is_selectedSourceEdge_both
#print axioms StructuralRamsey.Girth.track1_controlled_selectedPhysicalIntersections

end StructuralRamsey.Girth

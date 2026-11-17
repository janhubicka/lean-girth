import Girth.Track1FullSelectedWitnessEmbeddings
import Girth.Track1ActualSelectedCoverage
import Girth.Track1ActualSelectedLiftPairwiseAllowed
import Girth.Track1ActualSelectedOwnerColourArrow
import Girth.Track1ActualSelectedBStrong
import Girth.Track1OwnerSplitGirth
import Girth.SupportGirthEmbeddingEquiv
import Girth.ForestActualRecursiveSupport
import Girth.Track1SplitSelectedMixedLF2

/-!
# Track 1: combine the actual selected coloured Ramsey witness interfaces

This theorem assembles the genuine old selected B-family into ONE
owner-split hypergraph, with ONE common linear order and the exact
union of its selected vertex carriers.

All its conclusions are derived: full induced ordered B embeddings,
physical edge coverage, arbitrary girth >=2, pairwise permitted intersections,
ACTUAL mixed LF2 for split selected B-pieces and all split edges,
and the actual r-edge Ramsey arrow. The girth parameter is arbitrary:
using g=2 gives ordinary linearity; g=3 gives triangle-free support.
In particular no edge-coveredness
of the original untrimmed EHN witness is postulated.

The selected EHN family must still supply its real arrow,
A-support girth, pairwise controlled B intersections, source
marked-degree-one (derived separately from the source restriction)
and monotonicity in the fresh EHN order.

This is a new integration candidate, not yet a kernel certificate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}
variable {UA VB V I Choice : Type v}

/-- All geometric and Ramsey assertions of the actual selected
owner-split coloured-edge witness on the exact USED vertex carrier.
The theorem is conditional only on the old genuine EHN selected
family, its source colour restrictions, and old support girth. -/
theorem track1_selectedColouredWitness_from_EHN_family
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    [LinearOrder VB] [LinearOrder V] [Finite V]
    (family : Choice → Embedding B C)
    (k : ℕ)
    (sourceColour : VB → I) (predicate : V → I)
    (allowed : Set I)
    (hRestricted : ∀ e f : Set VB,
      e ∈ supportCopies A B → f ∈ supportCopies A B → e ≠ f →
      ∀ x : VB, x ∈ e → x ∈ f → sourceColour x ∈ allowed)
    (hPredicate : ∀ c : Choice, ∀ x : VB,
      predicate (family c x) = sourceColour x)
    (hMono : ∀ c : Choice, StrictMono (family c))
    (hStrong : ∀ c : Choice,
      AStrong A C (copyCarrier (family c)))
    (hSupportInj : Function.Injective
      (fun c : Choice => bSupportPiece A (family c)))
    (hControlled : ∀ i j : Choice,
      ¬ SameCopy (family i) (family j) →
      (copyCarrier (family i) ∩ copyCarrier (family j)).Subsingleton ∨
        ∃ a : Embedding A C,
          copyCarrier (family i) ∩ copyCarrier (family j) =
            copyCarrier a)
    (g : ℕ) (hg : 2 ≤ g)
    (hAmbientGirth : GirthGT (supportCopies A C) g)
    {κ : Type w} [Nonempty κ]
    (hArrow : ∀ χ : Embedding A C → κ,
      ∃ c : Choice, ∀ a b : Embedding A B,
        χ ((family c).comp a) = χ ((family c).comp b)) :
    let H := selectedSupportOwnerSystem A family predicate allowed
    let selected : Choice → ColouredOwnerSelectedCopy (W := VB) H :=
      fun c => actualSelectedOwnerCopy A family predicate allowed c
        (track1_selectedForbiddenDegreeOne A family
          sourceColour predicate allowed hRestricted hPredicate c)
    ∃ o : LinearOrder H.Vertex,
      (∀ c : Choice,
        ∃ e : Embedding
          (colouredOrderedEdgeTarget k (supportCopies A B) sourceColour)
          ((@colouredOrderedEdgeTarget I H.Vertex k
              H.splitPhysicalEdges H.newPredicate o).induce
              (H.selectedLiftCarrierFor selected)),
          ∀ x : VB, (e x).1 = (selected c).lift x) ∧
      (∀ e : Set H.Vertex, e ∈ H.splitPhysicalEdges →
        e ⊆ H.selectedLiftCarrierFor selected) ∧
      GirthGT H.splitPhysicalEdges g ∧
      PairwiseAllowed (fun c : Choice =>
        (selected c).selectedLiftSupportPiece) ∧
      (∀ c : Choice, ∀ f : H.OldEdge, ∀ z w : H.Vertex,
        z ≠ w → z ∈ H.splitEdge f → w ∈ H.splitEdge f →
        z ∈ Set.range (selected c).lift →
        w ∈ Set.range (selected c).lift →
        ∃ a : (selected c).SourceEdge,
          (selected c).physicalEdge a = f) ∧
      LocalForestThrough
        (mixedOwnerSmall
          (fun c : Choice => (selected c).selectedLiftSupportPiece)
          (fun f : H.OldEdge => H.splitEdge f)) 2 ∧
      (∀ χ : H.SplitPhysicalEdge → κ,
        ∃ c : Choice,
          ∀ a b : (selected c).SourceEdge,
            χ (H.physicalSplitEdge ((selected c).physicalEdge a)) =
            χ (H.physicalSplitEdge ((selected c).physicalEdge b))) := by
  classical
  dsimp
  let H := selectedSupportOwnerSystem A family predicate allowed
  let selected : Choice → ColouredOwnerSelectedCopy (W := VB) H :=
    fun c => actualSelectedOwnerCopy A family predicate allowed c
      (track1_selectedForbiddenDegreeOne A family
        sourceColour predicate allowed hRestricted hPredicate c)
  have hForbid : ∀ c : Choice, ∀ (x : VB)
      (e f : {e : Set VB // e ∈ supportCopies A B}),
      predicate (family c x) ∉ allowed →
      x ∈ e.1 → x ∈ f.1 → e = f :=
    track1_selectedForbiddenDegreeOne A family sourceColour
      predicate allowed hRestricted hPredicate
  obtain ⟨o, hLifts⟩ :=
    track1_exists_actualSelectedColouredLifts A family
      k sourceColour predicate allowed hRestricted hPredicate hMono
  have hCovered : ∀ e : Set H.Vertex,
      e ∈ H.splitPhysicalEdges →
        e ⊆ H.selectedLiftCarrierFor selected :=
    track1_actualSelectedSplitEdges_covered A family predicate allowed hForbid
  have hOldSub : H.edges ⊆ supportCopies A C := by
    rintro e ⟨c, a, rfl⟩
    exact ⟨(family c).comp a, rfl⟩
  have hOldGirth : GirthGT H.edges g :=
    girthGT_of_subset hOldSub hAmbientGirth
  have hGirth : GirthGT H.splitPhysicalEdges g :=
    H.splitPhysicalEdges_girthGT g hOldGirth
  have hDifferent : ∀ ⦃i j : Choice⦄, i ≠ j →
      ¬ SameCopy (family i) (family j) := by
    intro i j hij hSame
    apply hij
    apply hSupportInj
    exact bSupportPiece_eq_of_sameCopy A (family i) (family j) hSame
  have hPair : PairwiseAllowed
      (fun c : Choice => (selected c).selectedLiftSupportPiece) :=
    track1_actualSelectedLiftPairwiseAllowed
      A family predicate allowed hForbid hDifferent hControlled
  have hStrongNew :
      ∀ c : Choice, ∀ f : H.OldEdge, ∀ z w : H.Vertex,
        z ≠ w → z ∈ H.splitEdge f → w ∈ H.splitEdge f →
        z ∈ Set.range (selected c).lift →
        w ∈ Set.range (selected c).lift →
        ∃ a : (selected c).SourceEdge,
          (selected c).physicalEdge a = f :=
    track1_actualSelectedBStrong_from_old
      A family predicate allowed hForbid hStrong
  have hMixedLF2 : LocalForestThrough
      (mixedOwnerSmall
        (fun c : Choice => (selected c).selectedLiftSupportPiece)
        (fun f : H.OldEdge => H.splitEdge f)) 2 :=
    track1_actualSplitSelected_mixedLF2 H selected
      hPair hStrongNew (girthGT_mono hGirth hg)
  have hOldArrow : ∀ χ : H.OldEdge → κ,
      ∃ c : Choice, ∀ a b : (selected c).SourceEdge,
        χ ((selected c).physicalEdge a) =
          χ ((selected c).physicalEdge b) :=
    actualSelectedOwner_oldColourArrow
      A family predicate allowed hArrow hForbid
  refine ⟨o, hLifts, hCovered, hGirth, hPair, hStrongNew,
    hMixedLF2, ?_⟩
  intro χ
  exact H.selectedColourTransfer selected hOldArrow χ

#print axioms StructuralRamsey.Girth.track1_selectedColouredWitness_from_EHN_family

end StructuralRamsey.Girth

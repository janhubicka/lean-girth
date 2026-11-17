import Girth.Track1ColouredSelectedWitnessAssembly
import Girth.Track1GeneralSelectedFamily
import Girth.Track1PhysicalSelectedRepresentatives
import Girth.Track5OwnerSplitMarkedCoverage
import Girth.Track1ColourFromRel
import Girth.LinearityGirthTwo

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v w

/-- The actual finite selected witness on the used split carrier. -/
abbrev CoveredMarkedColouredWitness
    {I VB : Type v} [LinearOrder VB]
    (k : ℕ) (E : Set (Set VB)) (targetColour : VB → I)
    (allowed : Set I) (κ : Type w) : Prop :=
    ∃ (W J : Type v) (H : ColouredEdgeOwnerSplit W I)
      (selected : J → ColouredOwnerSelectedCopy (W := VB) H)
      (order : LinearOrder H.Vertex),
      Finite H.Vertex ∧ Finite J ∧ H.allowed = allowed ∧
      (∀ j, (selected j).sourceEdges = E) ∧
      (∀ j x, H.newPredicate ((selected j).lift x) = targetColour x) ∧
      (∀ f : H.OldEdge, ∃ j, ∃ a : (selected j).SourceEdge,
        (selected j).physicalEdge a = f) ∧
      (∀ j, ∃ e : Embedding
        (colouredOrderedEdgeTarget k E targetColour)
        ((@colouredOrderedEdgeTarget I H.Vertex k
          H.splitPhysicalEdges H.newPredicate order).induce
          (H.selectedLiftCarrierFor selected)),
        ∀ x, (e x).1 = (selected j).lift x) ∧
      (∀ e ∈ H.splitPhysicalEdges, e ⊆ H.selectedLiftCarrierFor selected) ∧
      (∀ z : H.selectedLiftCarrierFor selected,
        ∃ e : H.SplitPhysicalEdge, z.1 ∈ e.1) ∧
      (∀ e f : H.SplitPhysicalEdge, e ≠ f →
        e.1 ∩ f.1 ⊆ {z | H.newPredicate z ∈ allowed}) ∧
      GirthGT H.splitPhysicalEdges 2 ∧
      PairwiseAllowed (fun j => (selected j).selectedLiftSupportPiece) ∧
      (∀ j, ∀ f : H.OldEdge, ∀ z y : H.Vertex,
        z ≠ y → z ∈ H.splitEdge f → y ∈ H.splitEdge f →
        z ∈ Set.range (selected j).lift → y ∈ Set.range (selected j).lift →
        ∃ a : (selected j).SourceEdge, (selected j).physicalEdge a = f) ∧
      LocalForestThrough
        (mixedOwnerSmall (fun j => (selected j).selectedLiftSupportPiece)
          (fun f : H.OldEdge => H.splitEdge f)) 2 ∧
      (∀ χ : H.SplitPhysicalEdge → κ, ∃ j,
        ∀ a b : (selected j).SourceEdge,
          χ (H.physicalSplitEdge ((selected j).physicalEdge a)) =
          χ (H.physicalSplitEdge ((selected j).physicalEdge b)))

/-- A linear, covered ordered coloured target with the given marked
edge intersections has an actual selected EHN Ramsey witness. Its used
vertex carrier is covered and distinct output edges meet only in the
allowed predicates. -/
theorem track5_exists_selectedColouredWitness_marked_covered
    {I VB : Type v} [LinearOrder I] [LinearOrder VB] [Finite VB]
    (k : ℕ) (hk : 2 ≤ k)
    (edgeColour : Fin k → I) (targetColour : VB → I)
    (E : Set (Set VB)) (allowed : Set I)
    (hSupport : supportCopies (colouredOrderedEdgeSource.{v, v} k edgeColour)
      (colouredOrderedEdgeTarget k E targetColour) = E)
    (hSourceCovered : ∀ x : VB, ∃ e ∈ E, x ∈ e)
    (hEdgeBlocks : ∀ x y, edgeColour x ≠ edgeColour y → x < y →
      edgeColour x < edgeColour y)
    (hTargetBlocks : ∀ x y, targetColour x < targetColour y → x < y)
    (hGirth : GirthGT E 2)
    (hRestricted : ∀ e f : Set VB, e ∈ E → f ∈ E → e ≠ f →
      ∀ x : VB, x ∈ e → x ∈ f → targetColour x ∈ allowed)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    CoveredMarkedColouredWitness k E targetColour allowed κ := by
  classical
  let A := colouredOrderedEdgeSource.{v, v} k edgeColour
  let B := colouredOrderedEdgeTarget k E targetColour
  have hAirr : A.Irreducible := by
    intro x y _
    refine ⟨.inl (.inl ()), (fun i => ULift.up i), x.down, y.down, ?_, rfl, rfl⟩
    exact ULift.up_injective
  change supportCopies A B = E at hSupport
  have hBgirth : GirthGT (supportCopies A B) 2 := hSupport ▸ hGirth
  have hBlinear : ALinear A B := by
    intro a b hDifferent
    exact (pairwise_subsingleton_of_girthGT_two hBgirth) ⟨a, rfl⟩ ⟨b, rfl⟩ hDifferent
  have hMono : ∀ a : Embedding A B, StrictMono a := by
    intro a x y hxy
    change x.down < y.down at hxy
    have hColour (z : ULift.{v} (Fin k)) :
        targetColour (a z) = edgeColour z.down := by
      exact (a.map_rel_iff (.inl (.inr (edgeColour z.down)))
        (fun _ : Fin 1 => z)).mpr (by rfl)
    by_cases hSame : edgeColour x.down = edgeColour y.down
    · have h := (a.map_rel_iff (.inr ()) ![x, y]).mpr (by
        change edgeColour x.down = edgeColour y.down ∧ x.down < y.down
        exact ⟨hSame, hxy⟩)
      change targetColour (a x) = targetColour (a y) ∧ a x < a y at h
      exact h.2
    · apply hTargetBlocks
      rw [hColour x, hColour y]
      exact hEdgeBlocks x.down y.down hSame hxy
  obtain ⟨W, hFinite, oldOrder, C, oldFamily, hClass, hOrder,
    hStrong, hOverlap, hArrow⟩ :=
    track1_selectedOrderedRamseyFamily_general A B hAirr hBlinear hMono κ
  letI : Finite W := hFinite
  letI : LinearOrder W := oldOrder
  let J := Track1PhysicalBCarrier oldFamily
  let family : J → Embedding B (closureRelReduct C) :=
    track1_physicalRepresentative oldFamily
  have hMember (j : J) : family j ∈ oldFamily :=
    (track1_physicalRepresentative_spec oldFamily j).1
  let default := edgeColour ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hk⟩
  let predicate := oldColourOfRel (closureRelReduct C) default
  have hPredicate (j : J) (x : VB) : predicate (family j x) = targetColour x :=
    oldColourOfRel_on_selected k E targetColour _ default (family j) x
  have hRestrict : ∀ e f : Set VB, e ∈ supportCopies A B →
      f ∈ supportCopies A B → e ≠ f →
      ∀ x, x ∈ e → x ∈ f → targetColour x ∈ allowed := by
    simpa only [hSupport] using hRestricted
  have hControlled : ∀ i j : J, ¬ SameCopy (family i) (family j) →
      (copyCarrier (family i) ∩ copyCarrier (family j)).Subsingleton ∨
      ∃ a : Embedding A (closureRelReduct C),
        copyCarrier (family i) ∩ copyCarrier (family j) = copyCarrier a := by
    intro i j hDifferent
    exact hOverlap (family i) (hMember i) (family j) (hMember j) hDifferent
  let H := selectedSupportOwnerSystem A family predicate allowed
  let selected : J → ColouredOwnerSelectedCopy (W := VB) H :=
    fun j => actualSelectedOwnerCopy A family predicate allowed j
      (track1_selectedForbiddenDegreeOne A family
        targetColour predicate allowed hRestrict hPredicate j)
  obtain ⟨order, hLift, hCover, hNewGirth, hPair, hNewStrong, hForest, hRamsey⟩ :=
    track1_selectedColouredWitness_from_EHN_family A family k targetColour
      predicate allowed hRestrict hPredicate
      (fun j x y hxy => hOrder (family j) (hMember j) x y hxy)
      (fun j => hStrong (family j) (hMember j))
      (track1_physicalRepresentative_supportPieces_injective A oldFamily)
      hControlled 2 (by decide)
      (girthGT_two_of_aLinear A (closureRelReduct C) hClass.1)
      (track1_physicalRepresentative_arrow A oldFamily hArrow)
  have hLocalCovered : ∀ j x, ∃ e : (selected j).SourceEdge, x ∈ e.1 := by
    intro j x
    obtain ⟨e, he, hx⟩ := hSourceCovered x
    refine ⟨⟨e, ?_⟩, hx⟩
    change e ∈ supportCopies A B
    rw [hSupport]
    exact he
  obtain ⟨hPoints, hMarked⟩ :=
    H.selectedLiftCarrierFor_marked_covered selected hLocalCovered
  have hOwned : ∀ f : H.OldEdge, ∃ (j : J) (e : (selected j).SourceEdge),
      (selected j).physicalEdge e = f :=
    track1_actualSelectedOldEdge_covered A family predicate allowed
      (track1_selectedForbiddenDegreeOne A family
        targetColour predicate allowed hRestrict hPredicate)
  have hFiniteJ : Finite J := by
    unfold J Track1PhysicalBCarrier
    infer_instance
  have hColours (j : J) (x : VB) :
      H.newPredicate ((selected j).lift x) = targetColour x :=
    (H.selectedLift_preserves_predicate (selected j) x).trans (hPredicate j x)
  refine ⟨W, J, H, selected, order, H.finite_ownerVertex, hFiniteJ, rfl,
    fun _ => hSupport, hColours, hOwned, ?_, hCover, hPoints, hMarked,
    hNewGirth, hPair, hNewStrong, hForest, hRamsey⟩
  rw [hSupport] at hLift
  exact hLift

#print axioms StructuralRamsey.Girth.track5_exists_selectedColouredWitness_marked_covered

end StructuralRamsey.Girth

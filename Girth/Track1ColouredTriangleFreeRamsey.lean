import Girth.Track1ColouredSelectedWitnessAssembly
import Girth.Track1TriangleFreePhysicalFamily
import Girth.Track1ColourFromRel
import Girth.LinearityGirthTwo

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v w

/-- A triangle-free ordered coloured edge target has a finite selected
Ramsey witness. The positive split support and the selected induced lifts
use the same physical edges and the same common order. -/
theorem track1_exists_selectedColouredWitness_triangleFree
    {I VB : Type v} [LinearOrder I] [LinearOrder VB] [Finite VB]
    (k : ℕ) (hk : 2 ≤ k)
    (edgeColour : Fin k → I) (targetColour : VB → I)
    (E : Set (Set VB)) (allowed : Set I)
    (hEnumerate : ∀ e ∈ E, ∃ ι : Fin k ↪ VB,
      Set.range (ι : Fin k → VB) = e ∧
      (∀ x, targetColour (ι x) = edgeColour x) ∧
      (∀ x y, edgeColour x = edgeColour y → (x < y ↔ ι x < ι y)))
    (hEdgeBlocks : ∀ x y, edgeColour x ≠ edgeColour y → x < y →
      edgeColour x < edgeColour y)
    (hTargetBlocks : ∀ x y, targetColour x < targetColour y → x < y)
    (hGirth : GirthGT E 3)
    (hRestricted : ∀ e f : Set VB, e ∈ E → f ∈ E → e ≠ f →
      ∀ x : VB, x ∈ e → x ∈ f → targetColour x ∈ allowed)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W J : Type v) (H : ColouredEdgeOwnerSplit W I)
      (selected : J → ColouredOwnerSelectedCopy (W := VB) H)
      (order : LinearOrder H.Vertex),
      Finite H.Vertex ∧ H.allowed = allowed ∧
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
      GirthGT H.splitPhysicalEdges 3 ∧
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
          χ (H.physicalSplitEdge ((selected j).physicalEdge b))) := by
  classical
  let A := colouredOrderedEdgeSource.{v, v} k edgeColour
  let B := colouredOrderedEdgeTarget k E targetColour
  have hAirr : A.Irreducible := by
    intro x y _
    refine ⟨.inl (.inl ()), (fun i => ULift.up i), x.down, y.down, ?_, rfl, rfl⟩
    exact ULift.up_injective
  have hSupport : supportCopies A B = E :=
    colouredOrderedEdgeSupport_exact k E edgeColour targetColour hEnumerate
  have hBgirth : GirthGT (supportCopies A B) 3 := hSupport ▸ hGirth
  have hBlinear : ALinear A B := by
    intro a b hDifferent
    exact (pairwise_subsingleton_of_girthGT_two
      (girthGT_mono hBgirth (by decide))) ⟨a, rfl⟩ ⟨b, rfl⟩ hDifferent
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
  obtain ⟨W, hFinite, oldOrder, C, J, family, hClass, hInj, hOrder,
    hStrong, hOverlap, hArrow⟩ :=
    track1_triangleFreeRamsey_physicalSelectedFamily
      A B hAirr hBlinear hBgirth hMono κ
  letI : Finite W := hFinite
  letI : LinearOrder W := oldOrder
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
    exact hOverlap i j (fun h => hDifferent (h ▸ sameCopy_refl (family i)))
  let H := selectedSupportOwnerSystem A family predicate allowed
  let selected : J → ColouredOwnerSelectedCopy (W := VB) H :=
    fun j => actualSelectedOwnerCopy A family predicate allowed j
      (track1_selectedForbiddenDegreeOne A family
        targetColour predicate allowed hRestrict hPredicate j)
  obtain ⟨order, hLift, hCover, hNewGirth, hPair, hNewStrong, hForest, hRamsey⟩ :=
    track1_selectedColouredWitness_from_EHN_family A family k targetColour
      predicate allowed hRestrict hPredicate (fun j _ _ => hOrder j _ _)
      hStrong hInj hControlled 3 (by decide) hClass.2 hArrow
  have hPart (j : J) (x : VB) : H.newPredicate ((selected j).lift x) = targetColour x :=
    (H.selectedLift_preserves_predicate (selected j) x).trans (hPredicate j x)
  have hOwned : ∀ f : H.OldEdge, ∃ j, ∃ a : (selected j).SourceEdge,
      (selected j).physicalEdge a = f :=
    track1_actualSelectedOldEdge_covered A family predicate allowed
      (track1_selectedForbiddenDegreeOne A family targetColour predicate allowed
        hRestrict hPredicate)
  refine ⟨W, J, H, selected, order, H.finite_ownerVertex, rfl,
    fun _ => hSupport, hPart, hOwned, ?_, hCover, hNewGirth, hPair, hNewStrong, hForest, hRamsey⟩
  rw [hSupport] at hLift
  exact hLift

#print axioms StructuralRamsey.Girth.track1_exists_selectedColouredWitness_triangleFree

end StructuralRamsey.Girth

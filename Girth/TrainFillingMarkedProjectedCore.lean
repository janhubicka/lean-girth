import Girth.TrainFillingMarkedSparseSupport
import Girth.TrainFillingRestoreSelectedRelations

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.ColouredEdgeOwnerSplit

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v
variable {K : RelLanguage.{u}} {V A W I : Type v} [LinearOrder A]
variable (H : ColouredEdgeOwnerSplit V A)
variable (selected : I → ColouredOwnerSelectedCopy (W := W) H)
variable (A₀ : RelStructure K A) (Target : System K.withOrder A W)

local notation "Used" => H.selectedLiftCarrierFor selected

variable (hSource : ∀ i, (selected i).sourceEdges = supportCopies A₀.ordered Target.toRelStructure)
variable (hPart : ∀ i x, H.newPredicate ((selected i).lift x) = Target.part x)
variable (hFine : ∀ (a : Embedding A₀.ordered Target.toRelStructure) u, Target.part (a u) = u)
variable (hProjection : Target.toRelStructure.IsHomomorphism A₀.ordered Target.part)
variable (hNonempty : Nonempty (Embedding A₀.ordered Target.toRelStructure))
variable (hCover : ∀ x : W, ∃ a : Embedding A₀.ordered Target.toRelStructure, x ∈ copyCarrier a)
variable (hPair : PairwiseAllowed (fun i => (selected i).selectedLiftSupportPiece))

include A₀ hSource hPart hFine hProjection hNonempty hCover hPair in
/-- Tuples shared by two marked lifts agree in the full language.
A tuple with two distinct entries pulls back from their common selected
edge. A constant tuple uses vertex coverage and an empty tuple any edge. -/
theorem markedUsedLift_agrees_of_pairwise_support
    (i j : I) (r : K.withOrder.Symbol) (z w : Fin (K.withOrder.arity r) → W)
    (hEq : H.markedUsedLift selected i ∘ z = H.markedUsedLift selected j ∘ w)
    (hw : Target.rel r w) : Target.rel r z := by
  classical
  by_cases hij : i = j
  · subst j
    have hTuple : z = w :=
      funext (fun k => (H.markedUsedLift selected i).injective (congrFun hEq k))
    exact hTuple.symm ▸ hw
  have hParts : Target.part ∘ z = Target.part ∘ w := by
    funext k
    exact (hPart i (z k)).symm.trans
      ((congrArg (fun y : Used => H.newPredicate y.1) (congrFun hEq k)).trans (hPart j (w k)))
  have hTruth : A₀.ordered.rel r (Target.part ∘ z) := hParts.symm ▸ hProjection r w hw
  have hOnEdge : ∃ a : Embedding A₀.ordered Target.toRelStructure, ∀ k, z k ∈ copyCarrier a := by
    by_cases hIndex : Nonempty (Fin (K.withOrder.arity r))
    · obtain ⟨k₀⟩ := hIndex
      by_cases hDistinct : ∃ k, z k ≠ z k₀
      · obtain ⟨k, hk⟩ := hDistinct
        have hIn (q : Fin (K.withOrder.arity r)) :
            (selected i).lift (z q) ∈ Set.range (selected i).lift ∩ Set.range (selected j).lift :=
          ⟨⟨z q, rfl⟩, ⟨w q, (congrArg (fun y : Used => y.1) (congrFun hEq q)).symm⟩⟩
        rcases hPair hij with hSmall | ⟨e, hi, _hj, hOverlap⟩
        · exact (hk ((selected i).lift_injective (hSmall (hIn k) (hIn k₀)))).elim
        · obtain ⟨s, hs⟩ := hi
          change Set.range (selected i).lift ∩ Set.range (selected j).lift = e at hOverlap
          have hsSource : s.1 ∈ supportCopies A₀.ordered Target.toRelStructure := (hSource i) ▸ s.2
          obtain ⟨a, ha⟩ := hsSource
          refine ⟨a, fun q => ?_⟩
          have hImage : (selected i).lift (z q) ∈ (selected i).lift '' copyCarrier a := by
            rw [← ha, (selected i).lift_source_edge s, ← hs, ← hOverlap]
            exact hIn q
          obtain ⟨x, hx, hEqual⟩ := hImage
          exact (selected i).lift_injective hEqual ▸ hx
      · obtain ⟨a, ha⟩ := hCover (z k₀)
        exact ⟨a, fun k => (Classical.not_not.mp (fun h => hDistinct ⟨k, h⟩)).symm ▸ ha⟩
    · obtain ⟨a⟩ := hNonempty
      exact ⟨a, fun k => (hIndex ⟨k⟩).elim⟩
  obtain ⟨a, ha⟩ := hOnEdge
  choose u hu using ha
  have hTuple : a ∘ u = z := funext hu
  have hAtParts : Target.part ∘ z = u := by
    funext k
    change Target.part (z k) = u k
    rw [← hu k, hFine]
  exact hTuple ▸ (a.map_rel_iff r u).mpr (hAtParts ▸ hTruth)

include hSource hPart hFine hProjection hNonempty hCover hPair in
/-- Restore every projected relation on the actual marked lifts, while
preserving their literal physical edges and fine coordinates. -/
theorem exists_projectedMarkedCore [Finite A]
    (hOwned : ∀ f : H.OldEdge, ∃ i, ∃ a : (selected i).SourceEdge,
      (selected i).physicalEdge a = f)
    (hStrong : ∀ i (f : H.OldEdge) (x y : H.Vertex),
      x ≠ y → x ∈ H.splitEdge f → y ∈ H.splitEdge f →
      x ∈ Set.range (selected i).lift → y ∈ Set.range (selected i).lift →
      ∃ a : (selected i).SourceEdge, (selected i).physicalEdge a = f)
    (r : K.Symbol) (z : Fin (K.arity r) → A) (hSpan : Function.Surjective z) (hz : A₀.rel r z) :
    ∃ (R : System K.withOrder A Used) (f : I → StructuralRamsey.Partite.Embedding Target R),
      R.part = (fun y : Used => H.newPredicate y.1) ∧
      supportCopies A₀.ordered R.toRelStructure = Set.range (H.markedUsedEdgeCarrier selected) ∧
      (∀ i x, f i x = H.markedUsedLift selected i x) ∧
      (∀ (a : Embedding A₀.ordered R.toRelStructure) u, R.part (a u) = u) ∧
      R.toRelStructure.IsHomomorphism A₀.ordered R.part := by
  let edges := Set.range (H.markedUsedEdgeCarrier selected)
  let part (y : Used) := H.newPredicate y.1
  let lift := H.markedUsedLift selected
  let hOnEdge := H.markedUsed_partsOnEdges selected A₀ Target hSource hPart hFine hOwned
  let hInj := fun e he => (hOnEdge e he).1
  let R := restoreSelectedFillingRelations A₀ Target edges part lift hInj hPart
  have hExact := H.markedUsedLift_strong_of_exactSupport selected A₀ Target hSource hStrong
  have hAgree := H.markedUsedLift_agrees_of_pairwise_support selected A₀ Target
    hSource hPart hFine hProjection hNonempty hCover hPair
  let f := restoredFillingTarget A₀ Target edges part lift hInj hPart
    hNonempty hCover hExact hFine hProjection hAgree
  refine ⟨R, f, rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · exact supportCopies_restoreSelectedFillingRelations A₀ Target edges part lift hInj hPart
      (fun e he => (hOnEdge e he).2) hNonempty hCover hExact hFine hProjection hAgree
      (H.markedUsedLift_mem_edge_of_source selected A₀ Target hSource) r z hSpan hz
  · exact restoredFillingCore_fine A₀ Target edges part lift hInj hPart
  · exact restoreSelectedFillingRelations_projects A₀ Target edges part lift hInj hPart

end StructuralRamsey.Girth.ColouredEdgeOwnerSplit

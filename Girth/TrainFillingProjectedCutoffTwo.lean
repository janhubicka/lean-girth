import Girth.TrainFillingProjectedFirstWagonMarked
import Girth.TrainFillingMarkedProjectedCore
import Girth.TrainFillingMarkedLocalContraction
import Girth.TrainFillingApplyConcreteShorterOrder
import Girth.TrainFillingRealizeShorterOrder
import Girth.TrainPhysicalProjectedRankFromLocalFilling
import Girth.TrainFillingPrivateColourBlockOrder
import Girth.TrainRecursiveInitialTailGirth

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 0

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure
open StructuralRamsey.Girth.IndexedPrivateChoice

universe v

/-- Construct the actual local cutoff-two witness from the uniform
shorter order assertion, keeping the same marked and selected maps
through the literal contraction, filling and physical Ramsey arrow. -/
theorem cutoffTwoLocalFillingFromShorterOrder_constructed :
    CutoffTwoLocalFillingFromShorterOrder.{v, v} := by
  intro tail ht hOrder K A _ _ _ _ A₀ hSpanning κ _ _
  intro V _ Target original allowed hProjection hFine hCover hTwo hLinear hParameters hCuts
  classical
  obtain ⟨r, tuple, hTuple, hSpan⟩ := hSpanning
  obtain ⟨a₀, b₀, _⟩ := hTwo
  let Small := A₀.ordered
  have hOrderedSpan : HasSpanningRelation Small :=
    ⟨Sum.inl r, tuple, hTuple, hSpan⟩
  letI : Fintype V := Fintype.ofFinite V
  let baseOrder : LinearOrder V := LinearOrder.lift'
    (Fintype.equivFin V) (Fintype.equivFin V).injective
  letI : LinearOrder V := baseOrder
  letI : LinearOrder V := colourBlockOrder Target.part
  letI : Fintype A := Fintype.ofFinite A
  let k := Fintype.card A
  let enumA : Fin k ≃o A := Fintype.orderIsoFinOfCardEq A rfl
  have hk : 2 ≤ k := Fintype.one_lt_card
  let j₀ : Fin tail.length := ⟨0, List.length_pos_iff.mpr ht.nonempty⟩
  let cut : Fin (tail.length + 1 + 1) := (0 : Fin (tail.length + 1)).succ
  letI : Finite (OldACarrierEdge Small Target.toRelStructure) :=
    Finite.of_injective (fun e : OldACarrierEdge Small Target.toRelStructure => e.1)
      Subtype.val_injective
  letI : Finite original.FirstWagon :=
    inferInstanceAs (Finite (Quotient (original.wagonSetoid cut)))
  let wagon := cutoffTwoFirstCarrier original Subtype.val
  letI : LinearOrder original.FirstWagon := original.wagonQuotientLinearOrder cut
  letI : LinearOrder (FirstWagonUnionVertex wagon) := firstWagonUnionOrder wagon Target.part
  let W := firstWagonSparseSystem Target wagon
  have hFirstLinear : ∀ p q : original.FirstWagon, p ≠ q → (wagon p ∩ wagon q).Subsingleton :=
    labelledGirthGT_two_pairwise_subsingleton (labelledGirthGT_mono (hCuts j₀)
      (ht.two_le _ (List.get_mem _ j₀)))
  have hFirstParam := hParameters 0 cut (by change (0 : ℕ) ≤ cut.val; omega) (by rfl)
  let hLocalCover := actualFirstWagon_localCoverage Small Target original
  have hWFine := firstWagonSparseSystem_fineEdges Small Target wagon hOrderedSpan hFine
  have hWProject := firstWagonSparseSystem_projects Small Target wagon hProjection
  have hWCover := firstWagonSparseSystem_covered Small Target wagon hLocalCover
  let u₀ := Classical.choice (inferInstance : Nonempty A)
  let p₀ := original.firstWagon (actualEdge a₀)
  have hu₀ : a₀ u₀ ∈ wagon p₀ :=
    original.edge_subset_ownerWagonCarrier Subtype.val cut (actualEdge a₀) ⟨u₀, rfl⟩
  obtain ⟨aW, _⟩ := hWCover ⟨p₀, a₀ u₀, hu₀⟩
  obtain ⟨O, C, H, selected, order, hHFinite, hCFinite, _, hSource, hColour,
    hOwned, hLift, _, hPoints, hMarked, hGirth, hPair, hStrong, _, hArrow⟩ :=
    actualProjectedFirstWagon_markedRamsey A₀ Target enumA hk original
      hOrderedSpan hFine hLinear hFirstLinear (allowed cut) hFirstParam κ
  obtain ⟨R, marked, hRPart, hRSupport, hMark, hRFine, _⟩ :=
    H.exists_projectedMarkedCore selected A₀ W hSource hColour hWFine hWProject
      ⟨aW⟩ hWCover hPair hOwned hStrong r tuple hSpan hTuple
  let X : Type v := H.selectedLiftCarrierFor selected
  letI : Finite C := hCFinite
  letI : Fintype C := Fintype.ofFinite C
  letI : LinearOrder C := LinearOrder.lift' (Fintype.equivFin C) (Fintype.equivFin C).injective
  letI : Finite H.Vertex := hHFinite
  letI : Finite X := inferInstanceAs (Finite (H.selectedLiftCarrierFor selected))
  letI : Fintype X := Fintype.ofFinite X
  let xOrder : LinearOrder X := H.markedUsedAuxOrder selected order
  letI : LinearOrder X := xOrder
  letI : PartialOrder X := xOrder.toPartialOrder
  letI : Preorder X := xOrder.toPreorder
  letI : LE X := xOrder.toLE
  letI : LT X := xOrder.toLT
  have hC : Nonempty C := by
    obtain ⟨c, _⟩ := hArrow (fun _ => Classical.choice (inferInstance : Nonempty κ))
    exact ⟨c⟩
  letI : Nonempty C := hC
  letI : Nonempty original.FirstWagon := ⟨p₀⟩
  letI : Nontrivial X := by
    obtain ⟨u, w, huw⟩ := exists_pair_ne A
    let c := Classical.choice hC
    exact ⟨⟨marked c (aW u), marked c (aW w),
      fun h => huw (aW.injective ((marked c).toEmbedding.injective h))⟩⟩
  let eu := @Fintype.orderIsoFinOfCardEq X xOrder _ (Fintype.card X) rfl
  let coord := eu.toEquiv
  let enumerate : X ≃ ULift.{v} (Fin (Fintype.card X)) := coord.symm.trans Equiv.ulift.symm
  have hEnumerate : @StrictMono (Fin (Fintype.card X)) X inferInstance xOrder.toPreorder
      (fun i => enumerate.symm (ULift.up i)) := eu.strictMono
  have hWBlocks (x y : FirstWagonUnionVertex wagon) (h : W.part x < W.part y) : x < y := by
    change firstWagonUnionOrderKey wagon Target.part x < firstWagonUnionOrderKey wagon Target.part y
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)
  have hMarkedOrder := H.markedUsedLift_strictMono selected order k
    (supportCopies Small W.toRelStructure) W.part hWBlocks hColour hLift
  let localCopy := cutoffTwoMarkedLocalCopy Target wagon H selected R marked
  have hLocalPart := cutoffTwoMarkedLocalCopy_part Target wagon H selected R marked
  have hVBlocks (x y : V) (h : Target.part x ≠ Target.part y) (hlt : x < y) :
      Target.part x < Target.part y :=
    @colourBlockOrder_blocks A V _ baseOrder Target.part x y h hlt
  have hLocalOrder := cutoffTwoMarkedLocalCopy_strictMono Target wagon H selected R marked hMark
    order hMarkedOrder (firstWagonSparseSummand_strictMono Target wagon hVBlocks)
  have hLocalStrong := cutoffTwoMarkedLocalCopy_strong A₀ Target wagon H selected R marked
    hMark hSource hRSupport hOrderedSpan hStrong
  have hTemplateCover :=
    cutoffTwoMarkedTemplate_cover A₀ wagon H selected R hRSupport hPoints
  have hContacts :=
    cutoffTwoMarkedTemplate_intersections A₀ wagon H selected R hRSupport
      (allowed cut) hRPart hGirth hMarked
  have hTemplateLinear : ALinear Small R.toRelStructure :=
    aLinear_of_oldACarrier_edges_inter_subsingleton Small R.toRelStructure
      (fun e f h => (hContacts e f h).1)
  have hTemplateParameter := fun e f h => (hContacts e f h).2
  have hXBlocks (x y : X) (h : R.part x ≠ R.part y) (hlt : @LT.lt X xOrder.toLT x y) :
      R.part x < R.part y := by
    rw [hRPart] at h ⊢
    exact H.markedUsedAuxOrder_blocks selected order x y h hlt
  have hLocalColour := fun c p x => (hLocalPart c p x).symm
  let prep := CutoffTwoContraction.ofLocalCopies (A₀ := A₀) (Target := Target) (R := R)
    (original := original) (enumerate := enumerate)
    localCopy hLocalStrong hLocalCover hFirstLinear hTemplateCover hCover
    hLocalColour hLocalOrder hEnumerate hXBlocks
  have hShorter := CutoffTwoContraction.ofLocalCopies_exists_shorterOrderWitness
    (A₀ := A₀) (Target := Target) (R := R) (original := original) (enumerate := enumerate)
    localCopy hLocalStrong hLocalCover hFirstLinear hTemplateCover hCover
    hLocalColour hLocalOrder hEnumerate hXBlocks ht allowed κ hParameters hCuts hOrder
  have hWord := cutoffTwoMarked_wordArrow A₀ Target wagon H selected R marked
    hMark hSource hRSupport κ aW hArrow
  have hLocalArrow := cutoffTwoMarked_privateWordArrow A₀ Target wagon H selected R marked
    κ hLocalStrong hLocalCover hWord
  letI : Finite (Vertex (cutoffTwoChoices A₀ Target R original
      prep.localCopy prep.localStrong prep.localCover)) := by infer_instance
  exact cutoffTwoRawLocalData_of_shorterOrderWitness ht A₀ Target R enumerate original prep
    allowed κ hFine hProjection ⟨a₀⟩ hRFine hLocalPart hTemplateLinear hTemplateParameter
    hLocalArrow r tuple hSpan hTuple hShorter

/-- The complete well-founded train Ramsey recursion at equal language
and carrier universes, with the cutoff-two generator supplied. -/
theorem projectedForestAndOrder_allAdmissible (t : List ℕ) (ht : Admissible t) :
    ProjectedForestEverySpanningType.{v, v} t ∧ ProjectedOrderEverySpanningType.{v, v} t :=
  projectedForestAndOrder_of_localFilling cutoffTwoLocalFillingFromShorterOrder_constructed t ht

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

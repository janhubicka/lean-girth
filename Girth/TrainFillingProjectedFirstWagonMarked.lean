import Girth.TrainFillingProjectedFirstWagon
import Girth.TrainFillingMarkedSparseSupport
import Girth.TrainFillingPrivateActualFirstWagonSource
import Girth.Track5CoveredMarkedRamsey
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v w
variable {K : RelLanguage.{u}} {A V : Type v}

theorem actualFirstWagon_localCoverage
    (Small : RelStructure K A) (Target : System K A V) {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge Small Target.toRelStructure) (m + 1)) :
    let wagon := T.wagonClassCarrier Subtype.val (0 : Fin (m + 1)).succ
    ∀ (p : T.FirstWagon) (x : {v : V // v ∈ wagon p}),
      ∃ a : Embedding Small (Target.toRelStructure.induce (wagon p)), x ∈ copyCarrier a := by
  dsimp only
  exact originalFirstWagonLocalCoverage Small Target.toRelStructure _ T.firstWagon
    (T.edge_subset_ownerWagonCarrier Subtype.val (0 : Fin (m + 1)).succ)
    (fun p x => T.ownerEdge_covers_wagonVertex Subtype.val (0 : Fin (m + 1)).succ p x.1 x.2)

/-- Choose the marked witness of the literal sparse first-wagon support.
The auxiliary complete coloured order is used by the marked Ramsey
theorem, while all its edges are the actual sparse support. -/
theorem actualProjectedFirstWagon_markedRamsey
    (A₀ : RelStructure K A) [LinearOrder A] [Nontrivial A]
    (Target : System K.withOrder A V) [LinearOrder V] [Finite V]
    {k : ℕ} (enumerate : Fin k ≃o A) (hk : 2 ≤ k) {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A₀.ordered Target.toRelStructure) (m + 1))
    (hSpanning : HasSpanningRelation A₀.ordered)
    (hFine : ∀ (a : Embedding A₀.ordered Target.toRelStructure) u, Target.part (a u) = u)
    (hLinear : ALinear A₀.ordered Target.toRelStructure)
    (hWagonLinear : ∀ p q : T.FirstWagon, p ≠ q →
      (T.wagonClassCarrier Subtype.val (0 : Fin (m + 1)).succ p ∩
        T.wagonClassCarrier Subtype.val (0 : Fin (m + 1)).succ q).Subsingleton)
    (allowed : Set A)
    (hParameter : TrainParentIntersectionBound
      (T.wagonClassCarrier Subtype.val 0)
      (T.wagonParent 0 (0 : Fin (m + 1)).succ (by change (0 : ℕ) ≤ _; omega))
      (Target.part ⁻¹' allowed))
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    let wagon := T.wagonClassCarrier Subtype.val (0 : Fin (m + 1)).succ
    letI : Finite (OldACarrierEdge A₀.ordered Target.toRelStructure) :=
      Finite.of_injective (fun e : OldACarrierEdge A₀.ordered Target.toRelStructure => e.1)
        Subtype.val_injective
    letI := T.wagonQuotientLinearOrder (0 : Fin (m + 1)).succ
    letI := firstWagonUnionOrder wagon Target.part
    let W := firstWagonSparseSystem Target wagon
    CoveredMarkedColouredWitness k
      (supportCopies A₀.ordered W.toRelStructure) W.part allowed κ := by
  classical
  let wagon := T.wagonClassCarrier Subtype.val (0 : Fin (m + 1)).succ
  letI : Finite (OldACarrierEdge A₀.ordered Target.toRelStructure) :=
    Finite.of_injective (fun e : OldACarrierEdge A₀.ordered Target.toRelStructure => e.1)
      Subtype.val_injective
  letI : Finite T.FirstWagon :=
    inferInstanceAs (Finite (Quotient (T.wagonSetoid (0 : Fin (m + 1)).succ)))
  letI := T.wagonQuotientLinearOrder (0 : Fin (m + 1)).succ
  letI := firstWagonUnionOrder wagon Target.part
  let W := firstWagonSparseSystem Target wagon
  let E := supportCopies A₀.ordered W.toRelStructure
  have hWFine := firstWagonSparseSystem_fineEdges A₀.ordered Target wagon hSpanning hFine
  have hWCover := firstWagonSparseSystem_covered A₀.ordered Target wagon
    (actualFirstWagon_localCoverage A₀.ordered Target T)
  have hExact : E = taggedFirstWagonEdges wagon (supportCopies A₀.ordered Target.toRelStructure) :=
    firstWagonSparseSystem_support_eq_tagged_of_spanning A₀.ordered Target wagon hSpanning
  have hGirth : GirthGT E 2 := by
    rw [hExact]
    apply girthGT_two_of_linearEdgeSet
    intro e f he hf hne
    exact taggedFirstWagonEdges_pairwise_subsingleton
      (oldACarrier_edges_inter_subsingleton_of_aLinear A₀.ordered Target.toRelStructure hLinear)
      ⟨e, he⟩ ⟨f, hf⟩ (fun hEq => hne (congrArg (fun a => a.1) hEq))
  apply track5_exists_selectedColouredWitness_marked_covered k hk enumerate W.part E allowed
  · exact sparseSupport_eq_colouredCompletion A₀ W k enumerate.toEquiv hWFine
  · intro w
    obtain ⟨a, ha⟩ := hWCover w
    exact ⟨copyCarrier a, ⟨a, rfl⟩, ha⟩
  · exact fun _ _ _ hlt => enumerate.strictMono hlt
  · intro x y hlt
    change firstWagonUnionOrderKey wagon Target.part x < firstWagonUnionOrderKey wagon Target.part y
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
  · exact hGirth
  · exact firstWagonSparseSystem_marked A₀.ordered Target T hSpanning hWagonLinear allowed hParameter

end StructuralRamsey.Girth

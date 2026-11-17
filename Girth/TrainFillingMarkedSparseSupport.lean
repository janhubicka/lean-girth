import Girth.Track5MarkedWitnessExactSupport
import Girth.TrainFillingMarkedOrderOverlap
import Mathlib.Order.Prod.Lex.Basic

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.ColouredEdgeOwnerSplit

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v
variable {K : RelLanguage.{u}} {V A W I : Type v}
variable (H : ColouredEdgeOwnerSplit V A)
variable (selected : I → ColouredOwnerSelectedCopy (W := W) H)

local notation "Used" => H.selectedLiftCarrierFor selected

/-- The vertex embedding of a marked copy into the actual used witness. -/
noncomputable def markedUsedLift (i : I) : W ↪ Used where
  toFun x := ⟨(selected i).lift x, ⟨i, x, rfl⟩⟩
  inj' := by
    intro x y h
    exact (selected i).lift_injective (congrArg Subtype.val h)

/-- A split edge read on the actual used witness vertex type. -/
def markedUsedEdgeCarrier (e : H.SplitPhysicalEdge) : Set Used :=
  (Subtype.val : Used → H.Vertex) ⁻¹' e.1

private theorem mem_range_markedUsedLift (i : I) (y : Used) :
    y ∈ Set.range (H.markedUsedLift selected i) ↔ y.1 ∈ Set.range (selected i).lift := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

/-- The full marked source edge remains exact on the induced carrier. -/
theorem markedUsedLift_image_sourceEdge (i : I) (a : (selected i).SourceEdge) :
    H.markedUsedEdgeCarrier selected (H.physicalSplitEdge ((selected i).physicalEdge a)) =
      H.markedUsedLift selected i '' a.1 := by
  ext y
  change y.1 ∈ H.splitEdge ((selected i).physicalEdge a) ↔
    y ∈ H.markedUsedLift selected i '' a.1
  rw [← (selected i).lift_source_edge a]
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, Subtype.ext hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- The marked overlap law keeps its actual edge witnesses on the used
vertex type. The `PairwiseAllowed` proof must come from this same family. -/
theorem markedUsedLift_pairwise_overlap
    (hPair : PairwiseAllowed (fun i => (selected i).selectedLiftSupportPiece))
    (i j : I) (hne : i ≠ j) :
    (Set.range (H.markedUsedLift selected i) ∩
      Set.range (H.markedUsedLift selected j)).Subsingleton ∨
      ∃ e ∈ Set.range (H.markedUsedEdgeCarrier selected),
        Set.range (H.markedUsedLift selected i) ∩
          Set.range (H.markedUsedLift selected j) = e := by
  rcases hPair hne with hSmall | ⟨e, hi, _hj, hMeet⟩
  · left
    intro x hx y hy
    apply Subtype.ext
    exact hSmall
      ⟨(H.mem_range_markedUsedLift selected i x).mp hx.1,
        (H.mem_range_markedUsedLift selected j x).mp hx.2⟩
      ⟨(H.mem_range_markedUsedLift selected i y).mp hy.1,
        (H.mem_range_markedUsedLift selected j y).mp hy.2⟩
  · obtain ⟨a, ha⟩ := hi
    change Set.range (selected i).lift ∩ Set.range (selected j).lift = e at hMeet
    right
    let edge := H.physicalSplitEdge ((selected i).physicalEdge a)
    refine ⟨H.markedUsedEdgeCarrier selected edge, ⟨edge, rfl⟩, ?_⟩
    ext y
    change (y ∈ Set.range (H.markedUsedLift selected i) ∧
      y ∈ Set.range (H.markedUsedLift selected j)) ↔
        y.1 ∈ H.splitEdge ((selected i).physicalEdge a)
    rw [H.mem_range_markedUsedLift selected i y, H.mem_range_markedUsedLift selected j y]
    change y.1 ∈ Set.range (selected i).lift ∩ Set.range (selected j).lift ↔
      y.1 ∈ H.splitEdge ((selected i).physicalEdge a)
    rw [hMeet, ha]

section AuxiliaryOrder

variable [LinearOrder A]

/-- Put the fine predicates in consecutive blocks, using the marked
witness's order inside each block. -/
noncomputable def markedUsedAuxOrder (order : LinearOrder H.Vertex) : LinearOrder Used := by
  letI : LinearOrder H.Vertex := order
  let key (y : Used) : A ×ₗ H.Vertex := toLex (H.newPredicate y.1, y.1)
  exact LinearOrder.lift' key (fun _ _ h => Subtype.ext (congrArg (fun p => (ofLex p).2) h))

/-- In the auxiliary order, two different predicates occur in the order
of their fine labels. -/
theorem markedUsedAuxOrder_blocks (order : LinearOrder H.Vertex) :
    ∀ x y : Used, H.newPredicate x.1 ≠ H.newPredicate y.1 →
      @LT.lt Used (H.markedUsedAuxOrder selected order).toLT x y →
      H.newPredicate x.1 < H.newPredicate y.1 := by
  letI : LinearOrder H.Vertex := order
  intro x y hDifferent hxy
  change toLex (H.newPredicate x.1, x.1) < toLex (H.newPredicate y.1, y.1) at hxy
  rcases Prod.Lex.toLex_lt_toLex.mp hxy with hLt | ⟨hEq, _⟩
  · exact hLt
  · exact (hDifferent hEq).elim

/-- The same marked lifts preserve the auxiliary order. The canonical
coloured embeddings handle pairs within a predicate, and the block
order handles pairs in different predicates. -/
theorem markedUsedLift_strictMono [LinearOrder W]
    (order : LinearOrder H.Vertex) (k : ℕ) (edges : Set (Set W)) (part : W → A)
    (hBlocks : ∀ x y, part x < part y → x < y)
    (hPart : ∀ i x, H.newPredicate ((selected i).lift x) = part x)
    (hLift : ∀ i, ∃ s : Embedding (colouredOrderedEdgeTarget k edges part)
        ((@colouredOrderedEdgeTarget A H.Vertex k H.splitPhysicalEdges H.newPredicate order).induce Used),
        ∀ x, (s x).1 = (selected i).lift x)
    (i : I) :
    @StrictMono W Used (inferInstance : Preorder W)
      (H.markedUsedAuxOrder selected order).toPreorder (H.markedUsedLift selected i) := by
  letI : LinearOrder H.Vertex := order
  intro x y hxy
  change toLex (H.newPredicate ((selected i).lift x), (selected i).lift x) <
    toLex (H.newPredicate ((selected i).lift y), (selected i).lift y)
  apply Prod.Lex.toLex_lt_toLex.mpr
  have hLe : part x ≤ part y := le_of_not_gt (fun hgt => (not_lt_of_gt hxy) (hBlocks y x hgt))
  rcases lt_or_eq_of_le hLe with hLt | hEq
  · exact Or.inl (by simpa only [hPart] using hLt)
  · obtain ⟨s, hs⟩ := hLift i
    have hOrder := (s.map_rel_iff (.inr ()) ![x, y]).mpr ⟨hEq, hxy⟩
    change H.newPredicate (s x).1 = H.newPredicate (s y).1 ∧ (s x).1 < (s y).1 at hOrder
    exact Or.inr ⟨by simpa only [hPart] using hEq,
      by simpa only [hs x, hs y] using hOrder.2⟩

end AuxiliaryOrder

section SparseSupport

variable [LinearOrder A]
variable (A₀ : RelStructure K A) (Target : System K.withOrder A W)
variable (hSource : ∀ i, (selected i).sourceEdges = supportCopies A₀.ordered Target.toRelStructure)
include hSource

local notation "Small" => A₀.ordered

/-- The split witness's marked strongness pulls an ambient edge back to an
actual ordered edge of the sparse source, on exactly the used carrier. -/
theorem markedUsedLift_strong_of_exactSupport
    (hStrong : ∀ i (f : H.OldEdge) (x y : H.Vertex),
      x ≠ y → x ∈ H.splitEdge f → y ∈ H.splitEdge f →
      x ∈ Set.range (selected i).lift → y ∈ Set.range (selected i).lift →
      ∃ a : (selected i).SourceEdge, (selected i).physicalEdge a = f)
    (i : I) (e : Set Used) (he : e ∈ Set.range (H.markedUsedEdgeCarrier selected))
    (x y : W) (hne : x ≠ y) (hx : H.markedUsedLift selected i x ∈ e)
    (hy : H.markedUsedLift selected i y ∈ e) :
    ∃ a : Embedding Small Target.toRelStructure, e = H.markedUsedLift selected i '' copyCarrier a := by
  obtain ⟨e, rfl⟩ := he
  obtain ⟨f, rfl⟩ := H.physicalSplitEdge_surjective e
  obtain ⟨s, hs⟩ := hStrong i f ((selected i).lift x) ((selected i).lift y)
    (fun h => hne ((selected i).lift_injective h)) hx hy ⟨x, rfl⟩ ⟨y, rfl⟩
  have hsSource : s.1 ∈ supportCopies Small Target.toRelStructure := (hSource i) ▸ s.2
  obtain ⟨a, ha⟩ := hsSource
  exact ⟨a, by rw [← hs, H.markedUsedLift_image_sourceEdge selected i s, ha]⟩

/-- Every sparse source edge still maps to a genuine split edge. -/
theorem markedUsedLift_mem_edge_of_source
    (i : I) (a : Embedding Small Target.toRelStructure) :
    H.markedUsedLift selected i '' copyCarrier a ∈ Set.range (H.markedUsedEdgeCarrier selected) := by
  have hsSource : copyCarrier a ∈ (selected i).sourceEdges := by
    rw [hSource i]
    exact ⟨a, rfl⟩
  let s : (selected i).SourceEdge := ⟨copyCarrier a, hsSource⟩
  exact ⟨H.physicalSplitEdge ((selected i).physicalEdge s), H.markedUsedLift_image_sourceEdge selected i s⟩

/-- A covered split witness has exactly one vertex of each fine part in
each physical split edge, as read on the used carrier. -/
theorem markedUsed_partsOnEdges
    (hPart : ∀ i x, H.newPredicate ((selected i).lift x) = Target.part x)
    (hFine : ∀ (a : Embedding Small Target.toRelStructure) u, Target.part (a u) = u)
    (hOwned : ∀ f : H.OldEdge, ∃ i, ∃ a : (selected i).SourceEdge,
      (selected i).physicalEdge a = f)
    (e : Set Used) (he : e ∈ Set.range (H.markedUsedEdgeCarrier selected)) :
    Set.InjOn (fun y : Used => H.newPredicate y.1) e ∧
      ∀ u : A, ∃ y ∈ e, H.newPredicate y.1 = u := by
  obtain ⟨e, rfl⟩ := he
  obtain ⟨f, rfl⟩ := H.physicalSplitEdge_surjective e
  obtain ⟨i, s, hs⟩ := hOwned f
  have hsSource : s.1 ∈ supportCopies Small Target.toRelStructure := (hSource i) ▸ s.2
  obtain ⟨a, ha⟩ := hsSource
  have hCoordinate (u : A) :
      H.newPredicate (H.markedUsedLift selected i (a u)).1 = u :=
    (hPart i (a u)).trans (hFine a u)
  rw [← hs, H.markedUsedLift_image_sourceEdge selected i s, ha]
  constructor
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩ _ ⟨_, ⟨v, rfl⟩, rfl⟩ hEq
    change H.newPredicate (H.markedUsedLift selected i (a u)).1 =
      H.newPredicate (H.markedUsedLift selected i (a v)).1 at hEq
    rw [hCoordinate, hCoordinate] at hEq
    exact congrArg (fun w => H.markedUsedLift selected i (a w)) hEq
  · intro u
    exact ⟨H.markedUsedLift selected i (a u), ⟨a u, ⟨u, rfl⟩, rfl⟩, hCoordinate u⟩

/-- Recover the sparse order on the same marked lifts while keeping all
of their physical edge labels and fine coordinates. -/
theorem exists_sparseMarkedCore [Finite A]
    (hPart : ∀ i x, H.newPredicate ((selected i).lift x) = Target.part x)
    (hForward : PartiteOrderCompatible Target)
    (hFine : ∀ (a : Embedding Small Target.toRelStructure) u, Target.part (a u) = u)
    (hPositive : ∀ r : K.Symbol, 0 < K.arity r)
    (hVertex : ∀ x : W, ∃ a : Embedding Small Target.toRelStructure, x ∈ copyCarrier a)
    (hSupported : ∀ (r : K.Symbol) (z : Fin (K.arity r) → W), Target.rel (.inl r) z →
      ∃ a : Embedding Small Target.toRelStructure, ∀ k, z k ∈ copyCarrier a)
    (hOwned : ∀ f : H.OldEdge, ∃ i, ∃ a : (selected i).SourceEdge,
      (selected i).physicalEdge a = f)
    (hStrong : ∀ i (f : H.OldEdge) (x y : H.Vertex),
      x ≠ y → x ∈ H.splitEdge f → y ∈ H.splitEdge f →
      x ∈ Set.range (selected i).lift → y ∈ Set.range (selected i).lift →
      ∃ a : (selected i).SourceEdge, (selected i).physicalEdge a = f)
    (hPair : PairwiseAllowed (fun i => (selected i).selectedLiftSupportPiece))
    (r : K.Symbol) (z : Fin (K.arity r) → A) (hSpan : Function.Surjective z) (hz : A₀.rel r z) :
    ∃ (R : System K.withOrder A Used) (f : I → StructuralRamsey.Partite.Embedding Target R),
      R.part = (fun y : Used => H.newPredicate y.1) ∧
      supportCopies Small R.toRelStructure = Set.range (H.markedUsedEdgeCarrier selected) ∧
      (∀ i x, f i x = H.markedUsedLift selected i x) ∧
      (∀ (a : Embedding Small R.toRelStructure) u, R.part (a u) = u) ∧
      R.toRelStructure.IsHomomorphism Small R.part := by
  let edges := Set.range (H.markedUsedEdgeCarrier selected)
  let part (y : Used) := H.newPredicate y.1
  let lift := H.markedUsedLift selected
  let hOnEdge := H.markedUsed_partsOnEdges selected A₀ Target hSource hPart hFine hOwned
  let hEdgeInj := fun e he => (hOnEdge e he).1
  let R := fineFillingCore A₀ Target edges part lift hEdgeInj
  have hExact := H.markedUsedLift_strong_of_exactSupport selected A₀ Target hSource hStrong
  have hAgree := markedOrder_agrees_of_pairwise_physical_overlap A₀ Target edges part lift
    hPart hForward hFine hExact (H.markedUsedLift_pairwise_overlap selected hPair)
  let f := fineFillingCore_lift A₀ Target edges part lift hEdgeInj hPart hForward
    (finePartite_supportedRelations A₀ Target hFine hSupported)
    hPositive hVertex hFine (H.markedUsedLift_mem_edge_of_source selected A₀ Target hSource)
    hExact hAgree
  refine ⟨R, f, rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · exact supportCopies_fineFillingCore A₀ Target edges part lift hEdgeInj
      (fun e he => (hOnEdge e he).2) r z hSpan hz
  · exact fineFillingCore_fine A₀ Target edges part lift hEdgeInj
  · intro s w hw
    cases s with
    | inl s => exact hw.1
    | inr s =>
        cases s
        exact hw.1

end SparseSupport

end StructuralRamsey.Girth.ColouredEdgeOwnerSplit

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open StructuralRamsey.Partite (System)

universe u v
variable {K : RelLanguage.{u}} {A W : Type v}

/-- Complete the auxiliary order on the already chosen physical support.
Each fine colour occurs once in the new edge type, so no within-colour
comparison on that type needs to be transported. -/
theorem sparseSupport_eq_colouredCompletion
    (A₀ : RelStructure K A) [LinearOrder A]
    (Target : System K.withOrder A W) [LinearOrder W]
    (k : ℕ) (enumerate : Fin k ≃ A)
    (hFine : ∀ (a : Embedding A₀.ordered Target.toRelStructure) u, Target.part (a u) = u) :
    let edges := supportCopies A₀.ordered Target.toRelStructure
    supportCopies (colouredOrderedEdgeSource.{v,v} k enumerate)
      (colouredOrderedEdgeTarget k edges Target.part) = edges := by
  dsimp only
  apply colouredOrderedEdgeSupport_exact
  rintro _ ⟨a, rfl⟩
  let ι : Fin k ↪ W := ⟨fun i => a (enumerate i), by
    intro i j hij
    exact enumerate.injective (a.injective hij)⟩
  refine ⟨ι, ?_, fun i => hFine a (enumerate i), ?_⟩
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨enumerate i, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨enumerate.symm u, congrArg (fun b => a b) (enumerate.apply_symm_apply u)⟩
  · intro i j hSame
    have hEq : i = j := enumerate.injective hSame
    subst j
    simp

end StructuralRamsey.Girth

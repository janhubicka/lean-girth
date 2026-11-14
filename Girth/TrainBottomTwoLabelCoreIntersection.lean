import Girth.ForestToSupremeBottom
import Girth.ForestDistinctBoundaryAllowed
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# A bottom two-cycle with distinct core-separated pieces is supreme

This isolates the *original* n=2 cycle from the long cut-indexed
witness reduction. At bottom, use all physical edge carriers as the
linear support family K. A designated member has the small-or-whole
core-boundary property. An edge member has the same property when the
core is A-strong. For two labels whose mutual intersection lies in
the core, the existing distinct-owner allowed-intersection theorem
makes their intersection allowable. The existing bottom two-cycle
lemma then gives a global original designated supreme plan, with
no assumption about A1 or a reduced witness copy.

No full local witness system-girth hypothesis is used here.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- All *actual* physical bottom edges form a linear edge family.
The support-edge type is not artificially restricted to core edges. -/
theorem BottomForestGeometry.allEdgeCarriers_linear
    (H : D.BottomForestGeometry) :
    LinearEdgeSet (Set.range D.edgeCarrier) := by
  intro e f he hf hef
  obtain ⟨a, rfl⟩ := he
  obtain ⟨b, rfl⟩ := hf
  have hab : a ≠ b := by
    intro h
    apply hef
    exact congrArg D.edgeCarrier h
  exact H.edge_linear a b hab

/-- An own-edge boundary certificate with unrestricted K also has
membership in the actual full physical A-support edge set. -/
theorem BottomForestGeometry.boundary_from_univ_to_allEdges
    (H : D.BottomForestGeometry) (S : Set V) (a : I ⊕ E)
    (hBoundary : SmallOrWholeEdgeBoundary
      (Set.univ : Set (Set V)) S (D.bottomForestPiece H a)) :
    SmallOrWholeEdgeBoundary
      (Set.range D.edgeCarrier) S (D.bottomForestPiece H a) := by
  rcases hBoundary with hSmall | ⟨edge, _hUniv, hePiece, hIntersection⟩
  · exact Or.inl hSmall
  · change edge ∈ D.edgeCarrier '' D.edges a at hePiece
    obtain ⟨e, he, rfl⟩ := hePiece
    exact Or.inr ⟨D.edgeCarrier e, ⟨e, rfl⟩,
      ⟨e, he, rfl⟩, hIntersection⟩

/-- The physical one-edge label meets an A-strong core either in at
most one vertex or in its complete edge. -/
theorem BottomForestGeometry.edgeLabel_smallOrWhole_core
    (H : D.BottomForestGeometry) (S : Set V)
    (hCoreStrong : ∀ e : E,
      ¬ (D.edgeCarrier e ∩ S).Subsingleton →
        D.edgeCarrier e ⊆ S)
    (e : E) :
    SmallOrWholeEdgeBoundary (Set.range D.edgeCarrier) S
      (D.bottomForestPiece H (.inr e)) := by
  by_cases hSmall : (D.edgeCarrier e ∩ S).Subsingleton
  · exact Or.inl hSmall
  · have hSub : D.edgeCarrier e ⊆ S := hCoreStrong e hSmall
    right
    refine ⟨D.edgeCarrier e, ⟨e, rfl⟩, ?_, ?_⟩
    · exact ⟨e, rfl, rfl⟩
    · change D.edgeCarrier e ∩ S = D.edgeCarrier e
      exact Set.inter_eq_left.mpr hSub

/-- Both original label sorts have genuine small-or-whole core boundaries.
For designated labels this is the actual B-support boundary; for edge
labels it is only A-strongness of the attached core. -/
theorem BottomForestGeometry.everyLabel_smallOrWhole_core
    (H : D.BottomForestGeometry) (S : Set V)
    (hCoreStrong : ∀ e : E,
      ¬ (D.edgeCarrier e ∩ S).Subsingleton →
        D.edgeCarrier e ⊆ S)
    (hDesignated : ∀ a : I ⊕ E, D.designated a →
      SmallOrWholeEdgeBoundary (Set.univ : Set (Set V)) S
        (D.bottomForestPiece H a))
    (a : I ⊕ E) :
    SmallOrWholeEdgeBoundary (Set.range D.edgeCarrier) S
      (D.bottomForestPiece H a) := by
  cases a with
  | inl i =>
      exact H.boundary_from_univ_to_allEdges D S (.inl i)
        (hDesignated (.inl i) trivial)
  | inr e =>
      exact H.edgeLabel_smallOrWhole_core D S hCoreStrong e

/-- For any two ORIGINAL output labels (not witness owner labels),
core-separated carriers and their complete boundaries imply exactly
the allowed intersection of the forest lemma. -/
theorem BottomForestGeometry.allowedIntersection_of_core_separated
    (H : D.BottomForestGeometry) (S : Set V)
    (hCoreStrong : ∀ e : E,
      ¬ (D.edgeCarrier e ∩ S).Subsingleton →
        D.edgeCarrier e ⊆ S)
    (hDesignated : ∀ a : I ⊕ E, D.designated a →
      SmallOrWholeEdgeBoundary (Set.univ : Set (Set V)) S
        (D.bottomForestPiece H a))
    (a b : I ⊕ E)
    (hCross : D.carrier a ∩ D.carrier b ⊆ S) :
    AllowedIntersection (D.bottomForestPiece H a)
      (D.bottomForestPiece H b) := by
  let family : Fin 2 → HypergraphPiece V :=
    fun j => if j = 0 then D.bottomForestPiece H a
      else D.bottomForestPiece H b
  have h0 : family 0 = D.bottomForestPiece H a := by
    simp [family]
  have h1 : family 1 = D.bottomForestPiece H b := by
    simp [family]
  have hBoundary : ∀ j : Fin 2,
      SmallOrWholeEdgeBoundary (Set.range D.edgeCarrier) S (family j) := by
    intro j
    fin_cases j
    · simpa [h0] using
        (H.everyLabel_smallOrWhole_core D S hCoreStrong hDesignated a)
    · simpa [h1] using
        (H.everyLabel_smallOrWhole_core D S hCoreStrong hDesignated b)
  have hCrossFamily : ∀ ⦃i j : Fin 2⦄, i ≠ j →
      (family i).carrier ∩ (family j).carrier ⊆ S := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · simpa only [h0, h1] using hCross
    · simpa only [h0, h1, Set.inter_comm] using hCross
    · exact False.elim (hij rfl)
  have hPair : PairwiseAllowed family :=
    pairwiseAllowed_of_distinctOwner_boundaries family S
      (Set.range D.edgeCarrier)
      (H.allEdgeCarriers_linear D) hBoundary hCrossFamily
  have hDifferent : (0 : Fin 2) ≠ 1 := by decide
  simpa only [h0, h1] using hPair hDifferent

/-- The original length-two cycle is already globally supreme when
its two whole label carriers meet only inside the core. The forest
argument obtains an ORIGINAL designated source label; it does not
assume that a geometric witness owner is a B-copy. -/
theorem BigCycle.two_bottom_supreme_of_core_separated
    (C : D.BigCycle 2) (H : D.BottomForestGeometry)
    (S : Set V)
    (hCoreStrong : ∀ e : E,
      ¬ (D.edgeCarrier e ∩ S).Subsingleton →
        D.edgeCarrier e ⊆ S)
    (hDesignated : ∀ a : I ⊕ E, D.designated a →
      SmallOrWholeEdgeBoundary (Set.univ : Set (Set V)) S
        (D.bottomForestPiece H a))
    (hCross : D.carrier (C.label 0) ∩
      D.carrier (C.label 1) ⊆ S) :
    C.HasSimultaneousSupreme := by
  exact C.hasSimultaneousSupreme_of_two_bottom_forest D H
    (H.allowedIntersection_of_core_separated D S
      hCoreStrong hDesignated (C.label 0) (C.label 1) hCross)

end StructuralRamsey.Girth.OrderOneData

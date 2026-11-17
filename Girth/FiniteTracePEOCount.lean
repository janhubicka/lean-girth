import Girth.FiniteTraceEliminationBags
import Girth.FiniteTraceConformalLocal

/-!
# Direct counting of maximal traces by a perfect elimination order

For Track 8 the clique-tree construction, its parent forest, and
deletion of contained/duplicate bags are ALL unnecessary.

Conformality identifies the distinct maximal nonempty ORIGINAL
traces with the maximal cliques of their pair graph. If that graph
has a perfect elimination order, each maximal clique is exactly
the elimination bag at its first vertex. Thus distinct maximal
traces have distinct first vertices, giving the sharp |Z| bound.

Together with the already proved-source local-completion-to-
conformality theorem, this reduces the remaining pure combinatorics
to chordality and the existence of a perfect elimination order.
The empty-Z case is included automatically (no maximal traces).

This module has NOT been kernel-compiled; #print axioms belongs to
the check gate before any manuscript validation mark is promoted.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Every maximal original trace is contained in the chosen vertex
set Z by its defining representation as F i intersect Z. -/
theorem maximalTrace_subset_Z
    (F : ι → Set W) (Z : Set W)
    (T : maximalNonemptyTraceSets F Z) :
    T.1 ⊆ Z := by
  obtain ⟨i, hi⟩ := T.property.2.1
  intro x hx
  rw [hi] at hx
  exact hx.2

/-- View an original maximal trace as an actual set of vertices of Z,
rather than as a subset of the ambient type W. -/
def maximalTraceVertices
    (F : ι → Set W) (Z : Set W)
    (T : maximalNonemptyTraceSets F Z) : Set Z :=
  {x : Z | x.1 ∈ T.1}

/-- Maximal nonempty traces are nonempty as sets of Z-vertices. -/
theorem maximalTraceVertices_nonempty
    (F : ι → Set W) (Z : Set W)
    (T : maximalNonemptyTraceSets F Z) :
    (maximalTraceVertices F Z T).Nonempty := by
  obtain ⟨x, hx⟩ := T.property.1
  have hxZ : x ∈ Z := maximalTrace_subset_Z F Z T hx
  exact ⟨⟨x, hxZ⟩, hx⟩

/-- Under conformality and a perfect elimination order of the
pair graph, each distinct maximal original trace is equal to
ONE elimination bag.  No join tree of maximal cliques is needed. -/
theorem maximalTrace_eq_eliminationBag
    [Finite W]
    (F : ι → Set W) (Z : Set W)
    [LinearOrder Z]
    (hConformal : TraceConformal F Z)
    (hPEO : IsPerfectEliminationOrder (tracePairGraph F Z))
    (T : maximalNonemptyTraceSets F Z) :
    ∃ v : Z,
      maximalTraceVertices F Z T =
        laterNeighborBag (tracePairGraph F Z) v := by
  classical
  letI : Fintype Z := Fintype.ofFinite _
  obtain ⟨i, hEq⟩ := T.property.2.1
  have hiMax : IsMaximalNonemptyTrace F Z i := by
    constructor
    · simpa only [← hEq] using T.property.1
    · intro j hij
      have hTj : T.1 ⊆ traceOn F Z j := by
        rw [hEq]
        exact hij
      have hjT : traceOn F Z j ⊆ T.1 :=
        T.property.2.2 j hTj
      simpa only [hEq] using hjT
  have hT_eq : maximalTraceVertices F Z T =
      traceVertices F Z i := by
    ext x
    change x.1 ∈ T.1 ↔ x.1 ∈ F i
    rw [hEq]
    simp only [traceOn, Set.mem_inter_iff, x.2, and_true]
  let K : Finset Z := (maximalTraceVertices F Z T).toFinset
  have hKnonempty : K.Nonempty := by
    obtain ⟨x, hx⟩ := maximalTraceVertices_nonempty F Z T
    exact ⟨x, by simpa [K] using hx⟩
  have hClique :
      (tracePairGraph F Z).IsClique (K : Set Z) := by
    simpa [K, hT_eq] using traceVertices_isClique F Z i
  have hMax :
      ∀ L : Set Z, (K : Set Z) ⊆ L →
        (tracePairGraph F Z).IsClique L →
          L ⊆ (K : Set Z) := by
    simpa [K, hT_eq] using
      (maximalTrace_isMaximalClique F Z hConformal i hiMax)
  obtain ⟨v, _, hBag⟩ :=
    maximalClique_eq_laterNeighborBag
      (tracePairGraph F Z) hPEO K hKnonempty hClique hMax
  exact ⟨v, by simpa [K] using hBag⟩

/-- Distinct maximal nonempty traces inject into Z by choosing
a vertex whose elimination bag equals the trace.  Equivalently,
the injection sends a maximal clique to its earliest vertex. -/
theorem maximalTrace_card_le_of_PEO
    [Fintype W]
    (F : ι → Set W) (Z : Set W)
    [LinearOrder Z]
    (hConformal : TraceConformal F Z)
    (hPEO : IsPerfectEliminationOrder (tracePairGraph F Z)) :
    Nat.card (maximalNonemptyTraceSets F Z) ≤ Nat.card Z := by
  classical
  letI : Fintype Z := Fintype.ofFinite _
  letI : Fintype (maximalNonemptyTraceSets F Z) :=
    Fintype.ofFinite _
  have hWitness (T : maximalNonemptyTraceSets F Z) :
      ∃ v : Z, maximalTraceVertices F Z T =
        laterNeighborBag (tracePairGraph F Z) v :=
    maximalTrace_eq_eliminationBag F Z hConformal hPEO T
  choose rep hRep using hWitness
  have hInj : Function.Injective rep := by
    intro T U hEqualRep
    have hEqualSets :
        maximalTraceVertices F Z T =
          maximalTraceVertices F Z U := by
      calc
        maximalTraceVertices F Z T =
            laterNeighborBag (tracePairGraph F Z) (rep T) :=
          hRep T
        _ = laterNeighborBag (tracePairGraph F Z) (rep U) := by
          rw [hEqualRep]
        _ = maximalTraceVertices F Z U := (hRep U).symm
    apply Subtype.ext
    apply Set.ext
    intro x
    constructor
    · intro hxT
      have hxZ : x ∈ Z := maximalTrace_subset_Z F Z T hxT
      have hxU : (⟨x, hxZ⟩ : Z) ∈
          maximalTraceVertices F Z U := by
        rw [← hEqualSets]
        exact hxT
      exact hxU
    · intro hxU
      have hxZ : x ∈ Z := maximalTrace_subset_Z F Z U hxU
      have hxT : (⟨x, hxZ⟩ : Z) ∈
          maximalTraceVertices F Z T := by
        rw [hEqualSets]
        exact hxU
      exact hxT
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_le_of_injective rep hInj)

/-- The exact sharp conclusion of the small-trace lemma, including
empty Z and duplicate cover labels.  No maximal-clique join-tree
hypothesis appears anywhere in this theorem. -/
theorem smallTrace_selection_of_PEO
    [Fintype W] [Finite ι]
    (F : ι → Set W) (Z : Set W)
    [LinearOrder Z]
    (hConformal : TraceConformal F Z)
    (hPEO : IsPerfectEliminationOrder (tracePairGraph F Z)) :
    ∃ selected : Set ι,
      CoversNonemptyTraces F Z selected ∧
      selected.ncard ≤ Z.ncard := by
  classical
  refine ⟨Set.range (maximalTraceRepresentative F Z),
    maximalTraceRepresentatives_cover F Z, ?_⟩
  calc
    (Set.range (maximalTraceRepresentative F Z)).ncard =
        Nat.card (maximalNonemptyTraceSets F Z) := by
      exact Set.ncard_range_of_injective
        (maximalTraceRepresentative_injective F Z)
    _ ≤ Nat.card Z :=
      maximalTrace_card_le_of_PEO F Z hConformal hPEO
    _ = Z.ncard := by
      letI : Fintype Z := Fintype.ofFinite _
      simpa only [Nat.card_eq_fintype_card] using
        (Set.fintypeCard_eq_ncard Z)

/-- Local internal completions already give conformality.
Thus, with a perfect elimination order of the trace pair graph,
the entire sharp small-trace conclusion follows directly.
The only unresolved graph-theoretic input is existence of a
perfect elimination order from chordality. -/
theorem smallTrace_selection_of_local_completions_and_PEO
    [Fintype W] [Fintype ι]
    (F : ι → Set W) (Z : Set W) (q : ℕ)
    [LinearOrder Z]
    (hCover : ∀ x : W, x ∈ Z → ∃ i : ι, x ∈ F i)
    (hLocal : HasInternalJoinTreeCompletions F q)
    (hBudget : Z.ncard ≤ q)
    (hPEO : IsPerfectEliminationOrder (tracePairGraph F Z)) :
    ∃ selected : Set ι,
      CoversNonemptyTraces F Z selected ∧
      selected.ncard ≤ Z.ncard := by
  exact smallTrace_selection_of_PEO F Z
    (traceConformal_of_local_completion F Z q
      hCover hLocal hBudget) hPEO

end StructuralRamsey.Girth

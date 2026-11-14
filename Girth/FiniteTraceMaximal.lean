import Girth.FiniteTraceCoverage
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Card

/-!
# Maximal nonempty traces represented by original cover members

A finite-indexed cover has a maximal original trace above every nonempty
trace.  This file chooses *one original index* for each distinct maximal
nonempty trace, so duplicate members do not inflate the selected family's
cardinality.

There is no chordal, Helly, or local-to-global hypothesis here.  Those
hypotheses enter only when bounding the number of distinct maximal
traces.  In particular, this module does not assert the final small-trace
theorem without its missing join-tree construction.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Restriction of the carrier of an original cover member to Z. -/
def traceOn (F : ι → Set W) (Z : Set W) (i : ι) : Set W :=
  F i ∩ Z

/-- Maximality is inclusion maximality among original traces; we exclude
the empty trace even when Z itself is empty. -/
def IsMaximalNonemptyTrace
    (F : ι → Set W) (Z : Set W) (j : ι) : Prop :=
  (traceOn F Z j).Nonempty ∧
    ∀ k : ι, traceOn F Z j ⊆ traceOn F Z k →
      traceOn F Z k ⊆ traceOn F Z j

/-- Maximalization uses only finiteness of the ORIGINAL cover's index
type and inclusion order on its trace sets. -/
theorem exists_maximal_nonempty_trace
    [Finite ι]
    (F : ι → Set W) (Z : Set W)
    (i : ι) (hi : (traceOn F Z i).Nonempty) :
    ∃ j : ι,
      IsMaximalNonemptyTrace F Z j ∧
      traceOn F Z i ⊆ traceOn F Z j := by
  classical
  let S : Set ι :=
    {j | traceOn F Z i ⊆ traceOn F Z j}
  have hiS : i ∈ S := Set.Subset.rfl
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨i, hiS⟩
  obtain ⟨j, hjS, hjMax⟩ :=
    Set.Finite.exists_maximalFor
      (fun j : ι => traceOn F Z j) S hSfinite hSnonempty
  have hij : traceOn F Z i ⊆ traceOn F Z j := hjS
  have hjNonempty : (traceOn F Z j).Nonempty := by
    obtain ⟨x, hx⟩ := hi
    exact ⟨x, hij hx⟩
  refine ⟨j, ⟨hjNonempty, ?_⟩, hij⟩
  intro k hjk
  have hkS : k ∈ S := hij.trans hjk
  exact hjMax k hkS hjk

/-- The set of *distinct* maximal nonempty trace sets.  Its elements
are subsets of Z and have actual original-cover witnesses. -/
def maximalNonemptyTraceSets
    (F : ι → Set W) (Z : Set W) : Set (Set W) :=
  {T | T.Nonempty ∧
    (∃ i : ι, T = traceOn F Z i) ∧
    ∀ k : ι, T ⊆ traceOn F Z k →
      traceOn F Z k ⊆ T}

/-- Choose an actual original cover member for each distinct maximal
nonempty trace.  The definition is noncomputable only because of
classical representative choice. -/
noncomputable def maximalTraceRepresentative
    (F : ι → Set W) (Z : Set W)
    (T : maximalNonemptyTraceSets F Z) : ι :=
  Classical.choose T.property.2.1

theorem maximalTraceRepresentative_spec
    (F : ι → Set W) (Z : Set W)
    (T : maximalNonemptyTraceSets F Z) :
    T.1 = traceOn F Z (maximalTraceRepresentative F Z T) :=
  Classical.choose_spec T.property.2.1

/-- Different maximal trace SETS choose different original indices. -/
theorem maximalTraceRepresentative_injective
    (F : ι → Set W) (Z : Set W) :
    Function.Injective (maximalTraceRepresentative F Z) := by
  intro T U h
  apply Subtype.ext
  calc
    T.1 = traceOn F Z (maximalTraceRepresentative F Z T) :=
      maximalTraceRepresentative_spec F Z T
    _ = traceOn F Z (maximalTraceRepresentative F Z U) := by rw [h]
    _ = U.1 := (maximalTraceRepresentative_spec F Z U).symm

/-- The representatives of distinct maximal nonempty traces dominate
EVERY nonempty trace.  This includes duplicate original members and
does not impose any join tree until the cardinality estimate. -/
theorem maximalTraceRepresentatives_cover
    [Finite ι]
    (F : ι → Set W) (Z : Set W) :
    CoversNonemptyTraces F Z
      (Set.range (maximalTraceRepresentative F Z)) := by
  classical
  intro i hi
  obtain ⟨j, hjMax, hij⟩ :=
    exists_maximal_nonempty_trace F Z i hi
  let T : maximalNonemptyTraceSets F Z :=
    ⟨traceOn F Z j, hjMax.1, ⟨j, rfl⟩, hjMax.2⟩
  refine
    ⟨maximalTraceRepresentative F Z T, ⟨T, rfl⟩, ?_⟩
  have hTraceEq :
      traceOn F Z j =
        traceOn F Z (maximalTraceRepresentative F Z T) :=
    maximalTraceRepresentative_spec F Z T
  change traceOn F Z i ⊆
    traceOn F Z (maximalTraceRepresentative F Z T)
  calc
    traceOn F Z i ⊆ traceOn F Z j := hij
    _ = traceOn F Z (maximalTraceRepresentative F Z T) := hTraceEq

/-- The maximal trace T, viewed as a bag on the vertex set Z.
Every such T is already contained in Z.  Support edges are irrelevant
to the running-intersection counting argument. -/
def maximalTracePiece
    (F : ι → Set W) (Z : Set W)
    (T : maximalNonemptyTraceSets F Z) :
    HypergraphPiece Z where
  carrier := {x : Z | x.1 ∈ T.1}
  edges := ∅
  edge_subset_carrier := by
    intro e he
    exact False.elim he

/-- A join tree on the DISTINCT maximal nonempty traces yields a
sharp cardinality bound by leaf-private-vertex charging.
The join tree is an explicit *input* here; deriving it from small
local completions is the outstanding combinatorial bridge. -/
theorem maximalTrace_card_le_of_joinTree
    [Fintype W]
    (F : ι → Set W) (Z : Set W)
    [Nonempty (maximalNonemptyTraceSets F Z)]
    (J : JoinTree (maximalTracePiece F Z)) :
    Nat.card (maximalNonemptyTraceSets F Z) ≤ Nat.card Z := by
  classical
  letI : Fintype (maximalNonemptyTraceSets F Z) := Fintype.ofFinite _
  letI : Fintype Z := Fintype.ofFinite _
  have hNonempty :
      ∀ T : maximalNonemptyTraceSets F Z,
        (maximalTracePiece F Z T).carrier.Nonempty := by
    intro T
    obtain ⟨x, hxT⟩ := T.property.1
    obtain ⟨i, hEq⟩ := T.property.2.1
    have hxZ : x ∈ Z := by
      rw [hEq] at hxT
      exact hxT.2
    exact ⟨⟨x, hxZ⟩, hxT⟩
  have hAntichain :
      ∀ ⦃T U : maximalNonemptyTraceSets F Z⦄,
        T ≠ U →
          ¬ (maximalTracePiece F Z T).carrier ⊆
            (maximalTracePiece F Z U).carrier := by
    intro T U hTU hSub
    have hTSubU : T.1 ⊆ U.1 := by
      intro x hxT
      obtain ⟨i, hEq⟩ := T.property.2.1
      have hxZ : x ∈ Z := by
        rw [hEq] at hxT
        exact hxT.2
      have hxU := hSub (show
        (⟨x, hxZ⟩ : Z) ∈ (maximalTracePiece F Z T).carrier
        from hxT)
      exact hxU
    obtain ⟨i, hUEq⟩ := U.property.2.1
    have hTSubTrace : T.1 ⊆ traceOn F Z i := by
      simpa only [← hUEq] using hTSubU
    have hTraceSubT := T.property.2.2 i hTSubTrace
    have hUSubT : U.1 ⊆ T.1 := by
      simpa only [hUEq] using hTraceSubT
    exact hTU (Subtype.ext
      (Set.Subset.antisymm hTSubU hUSubT))
  simpa only [Nat.card_eq_fintype_card] using
    (J.card_le_of_antichain hNonempty hAntichain)

/-- Exact conditional version of the last step of the small-trace
lemma: selected indices are ORIGINAL cover members (no invented
bags), they dominate every nonempty trace, and the number of
distinct maximal traces is at most the size of Z. -/
theorem maximalTrace_selection_of_joinTree
    [Fintype W] [Finite ι]
    (F : ι → Set W) (Z : Set W)
    [Nonempty (maximalNonemptyTraceSets F Z)]
    (J : JoinTree (maximalTracePiece F Z)) :
    ∃ selected : Set ι,
      CoversNonemptyTraces F Z selected ∧
      (∃ reps : maximalNonemptyTraceSets F Z → ι,
        Function.Injective reps ∧
        selected = Set.range reps) ∧
      Nat.card (maximalNonemptyTraceSets F Z) ≤ Nat.card Z := by
  classical
  refine ⟨Set.range (maximalTraceRepresentative F Z), ?_, ?_, ?_⟩
  · exact maximalTraceRepresentatives_cover F Z
  · exact ⟨maximalTraceRepresentative F Z,
      maximalTraceRepresentative_injective F Z, rfl⟩
  · exact maximalTrace_card_le_of_joinTree F Z J


/-- Numerically exact small-trace conclusion, *conditional* only on the
join tree of distinct maximal traces.  The number of selected ORIGINAL
cover members is bounded, not merely the number of maximal trace types. -/
theorem maximalTrace_selection_ncard_of_joinTree
    [Fintype W] [Finite ι]
    (F : ι → Set W) (Z : Set W)
    [Nonempty (maximalNonemptyTraceSets F Z)]
    (J : JoinTree (maximalTracePiece F Z)) :
    ∃ selected : Set ι,
      CoversNonemptyTraces F Z selected ∧
      selected.ncard ≤ Z.ncard := by
  classical
  letI : Fintype Z := Fintype.ofFinite _
  let reps := maximalTraceRepresentative F Z
  have hCard := maximalTrace_card_le_of_joinTree F Z J
  refine ⟨Set.range reps, maximalTraceRepresentatives_cover F Z, ?_⟩
  calc
    (Set.range reps).ncard =
        Nat.card (maximalNonemptyTraceSets F Z) := by
      exact Set.ncard_range_of_injective
        (maximalTraceRepresentative_injective F Z)
    _ ≤ Nat.card Z := hCard
    _ = Z.ncard := by
      simpa only [Nat.card_eq_fintype_card] using
        (Set.fintypeCard_eq_ncard Z)

/-- Final finite trace-cover formulation, including the empty case.
The ONE open combinatorial input is now stated transparently:
when any maximal nonempty trace exists, these distinct traces admit
a running-intersection join tree.  The local-to-global proof of that
input is the remaining chordality/conformality task. -/
theorem smallTrace_selection_of_maximalJoinTree
    [Fintype W] [Finite ι]
    (F : ι → Set W) (Z : Set W)
    (hTree :
      Nonempty (maximalNonemptyTraceSets F Z) →
        Nonempty (JoinTree (maximalTracePiece F Z))) :
    ∃ selected : Set ι,
      CoversNonemptyTraces F Z selected ∧
      selected.ncard ≤ Z.ncard := by
  classical
  by_cases hα : Nonempty (maximalNonemptyTraceSets F Z)
  · letI : Nonempty (maximalNonemptyTraceSets F Z) := hα
    obtain ⟨J⟩ := hTree hα
    exact maximalTrace_selection_ncard_of_joinTree F Z J
  · refine ⟨∅, ?_, by simp⟩
    intro i hi
    obtain ⟨j, hj, _⟩ :=
      exists_maximal_nonempty_trace F Z i hi
    have hn :
        Nonempty (maximalNonemptyTraceSets F Z) :=
      ⟨⟨traceOn F Z j, hj.1, ⟨j, rfl⟩, hj.2⟩⟩
    exact (hα hn).elim


end StructuralRamsey.Girth

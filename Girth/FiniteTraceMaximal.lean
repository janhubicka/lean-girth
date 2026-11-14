import Girth.FiniteTraceCoverage
import Mathlib.Order.Preorder.Finite

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
    Set.Finite.exists_maximal_wrt
      (f := fun j : ι => traceOn F Z j)
      (s := S) hSfinite hSnonempty
  have hij : traceOn F Z i ⊆ traceOn F Z j := hjS
  have hjNonempty : (traceOn F Z j).Nonempty := by
    obtain ⟨x, hx⟩ := hi
    exact ⟨x, hij hx⟩
  refine ⟨j, ⟨hjNonempty, ?_⟩, hij⟩
  intro k hjk
  have hkS : k ∈ S := hij.trans hjk
  have hEq : traceOn F Z j = traceOn F Z k :=
    hjMax k hkS hjk
  simpa only [hEq] using
    (Set.Subset.rfl : traceOn F Z k ⊆ traceOn F Z k)

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
        traceOn F Z (maximalTraceRepresentative F Z T) := by
    simpa only [T] using
      (maximalTraceRepresentative_spec F Z T)
  simpa only [traceOn, hTraceEq] using hij

end StructuralRamsey.Girth

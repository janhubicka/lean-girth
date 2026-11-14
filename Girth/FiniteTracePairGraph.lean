import Girth.FiniteTraceMaximal
import Mathlib.Combinatorics.SimpleGraph.Clique
import Girth.ForestTraceRestriction
import Girth.ForestJoinTreeHelly

/-!
# Pair graph and conformality interfaces for finite traces

The pair graph has an edge between two distinct vertices of Z exactly
when they occur together in an ORIGINAL cover member.  Every trace is
a clique.  Under the explicit conformality hypothesis (every nonempty
clique lies in an original trace), maximal nonempty traces coincide
with maximal nonempty cliques.

This is only the conformality-to-maximal-trace adapter, NOT a proof that
bounded internal completions imply chordality/conformality.  That
remaining step is tracked separately.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Vertices of Z belonging to an original cover member. -/
def traceVertices
    (F : ι → Set W) (Z : Set W) (i : ι) : Set Z :=
  {x : Z | x.1 ∈ F i}

/-- Pair graph of the trace hypergraph. -/
def tracePairGraph
    (F : ι → Set W) (Z : Set W) : SimpleGraph Z where
  Adj x y :=
    x ≠ y ∧ ∃ i : ι, x.1 ∈ F i ∧ y.1 ∈ F i
  symm := by
    intro x y hxy
    obtain ⟨hne, i, hxi, hyi⟩ := hxy
    exact ⟨hne.symm, i, hyi, hxi⟩
  loopless := by
    intro x hxx
    exact hxx.1 rfl

/-- Each original trace is a clique in the pair graph, even with
duplicate cover members and isolated vertices. -/
theorem traceVertices_isClique
    (F : ι → Set W) (Z : Set W) (i : ι) :
    (tracePairGraph F Z).IsClique (traceVertices F Z i) := by
  intro x hx y hy hne
  exact ⟨hne, i, hx, hy⟩

/-- Conformality means that every nonempty pairwise-adjacent vertex
set is contained in a *single original member*.  Empty cliques are
excluded because no original member need exist when the cover is empty. -/
def TraceConformal
    (F : ι → Set W) (Z : Set W) : Prop :=
  ∀ (K : Set Z), K.Nonempty →
    (tracePairGraph F Z).IsClique K →
    ∃ i : ι, K ⊆ traceVertices F Z i

/-- Every maximal nonempty original trace is a maximal clique,
provided conformality.  We do not invoke a chordal-graph theorem
here; that theorem is required only to construct a clique tree. -/
theorem maximalTrace_isMaximalClique
    (F : ι → Set W) (Z : Set W)
    (hConformal : TraceConformal F Z)
    (i : ι) (hi : IsMaximalNonemptyTrace F Z i) :
    ∀ K : Set Z,
      traceVertices F Z i ⊆ K →
      (tracePairGraph F Z).IsClique K →
      K ⊆ traceVertices F Z i := by
  intro K hIK hClique
  obtain ⟨x, hxTrace⟩ := hi.1
  have hxZ : x ∈ Z := hxTrace.2
  have hKnonempty : K.Nonempty :=
    ⟨⟨x, hxZ⟩, hIK hxTrace.1⟩
  obtain ⟨j, hKj⟩ := hConformal K hKnonempty hClique
  have hIj : traceOn F Z i ⊆ traceOn F Z j := by
    intro y hy
    have hyZ : y ∈ Z := hy.2
    have hyK : (⟨y, hyZ⟩ : Z) ∈ K := hIK hy.1
    exact ⟨hKj hyK, hyZ⟩
  have hJi : traceOn F Z j ⊆ traceOn F Z i := hi.2 j hIj
  intro y hyK
  exact (hJi ⟨hKj hyK, y.2⟩).1

/-- The converse for a maximal nonempty clique.  This is the
finite-trace interface that identifies the clique-tree bags with
distinct maximal original traces. -/
theorem maximalClique_has_maximalTrace
    (F : ι → Set W) (Z : Set W)
    (hConformal : TraceConformal F Z)
    (K : Set Z) (hK : K.Nonempty)
    (hClique : (tracePairGraph F Z).IsClique K)
    (hMax :
      ∀ L : Set Z, K ⊆ L →
        (tracePairGraph F Z).IsClique L → L ⊆ K) :
    ∃ i : ι, IsMaximalNonemptyTrace F Z i ∧
      K = traceVertices F Z i := by
  obtain ⟨i, hKi⟩ := hConformal K hK hClique
  have hIK : traceVertices F Z i ⊆ K :=
    hMax (traceVertices F Z i) hKi (traceVertices_isClique F Z i)
  have hEq : K = traceVertices F Z i :=
    Set.Subset.antisymm hKi hIK
  have hNonempty : (traceOn F Z i).Nonempty := by
    obtain ⟨x, hxK⟩ := hK
    have hxi : x.1 ∈ F i := hKi hxK
    exact ⟨x.1, ⟨hxi, x.2⟩⟩
  refine ⟨i, ⟨hNonempty, ?_⟩, hEq⟩
  intro j hij
  have hTraceSub :
      traceVertices F Z i ⊆ traceVertices F Z j := by
    intro x hx
    exact (hij ⟨hx, x.2⟩).1
  have hKj : K ⊆ traceVertices F Z j := by
    rw [hEq]
    exact hTraceSub
  have hJsubK :=
    hMax (traceVertices F Z j) hKj (traceVertices_isClique F Z j)
  intro x hxj
  have hxZ : x ∈ Z := hxj.2
  have hxK : (⟨x, hxZ⟩ : Z) ∈ K := hJsubK hxj.1
  have hxi : x ∈ F i := by
    rw [hEq] at hxK
    exact hxK
  exact ⟨hxi, hxZ⟩


/-- A genuine join tree of all ORIGINAL restricted bags is conformal.
The diagonal case uses the original cover of Z; distinct pairs are
covered by the definition of the pair graph.  The proof reuses the
direct leaf-induction Helly lemma and does not use any chordal result. -/
theorem traceConformal_of_joinTree
    (F : ι → Set W) (Z : Set W)
    [Fintype ι] [Nonempty ι]
    (J : JoinTree
      (fun i : ι => (setBagPiece (F i)).traceCarrier Z))
    (hCover :
      ∀ x : Z, ∃ i : ι, x.1 ∈ F i) :
    TraceConformal F Z := by
  intro K hK hClique
  have hPair :
      ∀ x : Z, x ∈ K →
        ∀ y : Z, y ∈ K →
          ∃ i : ι,
            x ∈ ((setBagPiece (F i)).traceCarrier Z).carrier ∧
            y ∈ ((setBagPiece (F i)).traceCarrier Z).carrier := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst y
      obtain ⟨i, hxi⟩ := hCover x
      exact ⟨i, hxi, hxi⟩
    · have hAdj : (tracePairGraph F Z).Adj x y :=
        hClique hx hy hxy
      obtain ⟨_, i, hxi, hyi⟩ := hAdj
      exact ⟨i, hxi, hyi⟩
  obtain ⟨i, hi⟩ :=
    J.pairCovered_in_one_bag hK hPair
  exact ⟨i, hi⟩


end StructuralRamsey.Girth

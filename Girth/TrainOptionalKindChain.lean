import Girth.TrainOptionalKindOrder
import Mathlib.Data.List.Chain
import Mathlib.Tactic

/-!
# Circulation: chain-local tests for numerical preservation

The preceding optional-block weight lemma uses a recursive predicate.
For applications to the physical replacement cycle it is more natural
to check (i) that an insertion in the first block has vertex entering
and right connectors, and (ii) that an insertion in any later block
has vertex connectors on both sides of its block boundary.

These are a simple List.IsChain relation and an initial-boundary
condition. The lemmas below derive the recursive invariant from
exactly those local tests. They also record that every optional
block retains its old right connector, including at the final index.

No output BigCycle, wagon linearity, or appendix assumption is used.
-/

namespace StructuralRamsey.Girth

/-- The next block has a vertex-vertex boundary whenever it inserts
a wagon. This is the local relation used across all source blocks. -/
def OptionalKindFollow
    (a b : CycleConnectorKind × Bool) : Prop :=
  b.2 = true → a.1 = .vertex ∧ b.1 = .vertex

/-- The initial block's entering boundary, used to close the cyclic
word at its last-to-first edge. -/
def OptionalKindFirst
    (enter : CycleConnectorKind)
    (a : CycleConnectorKind × Bool) : Prop :=
  a.2 = true → enter = .vertex ∧ a.1 = .vertex

/-- The two local word conditions imply the recursive conditions
needed by the numerical weight theorem. -/
theorem optionalKindValid_of_chain
    (enter : CycleConnectorKind)
    (blocks : List (CycleConnectorKind × Bool))
    (hChain : blocks.IsChain OptionalKindFollow)
    (hFirst : ∀ a ∈ blocks.head?, OptionalKindFirst enter a) :
    OptionalKindValid enter blocks := by
  induction blocks generalizing enter with
  | nil =>
      trivial
  | cons hd tail ih =>
      obtain ⟨hEdge, hTailChain⟩ :=
        (List.isChain_cons).mp hChain
      have hHd : OptionalKindFirst enter hd :=
        hFirst hd (by simp)
      have hTailFirst :
          ∀ b ∈ tail.head?, OptionalKindFirst hd.1 b := by
        intro b hb
        exact hEdge b hb
      have hTailValid := ih hd.1 hTailChain hTailFirst
      rcases hd with ⟨kind, flag⟩
      cases flag with
      | false =>
          simpa [OptionalKindValid] using hTailValid
      | true =>
          obtain ⟨hEnter, hKind⟩ := hHd rfl
          exact ⟨hEnter, hKind, hTailValid⟩

/-- Direct usable interface: a chain of valid optional blocks
preserves the entire literal walk's twice-weight. -/
theorem optionalKindWord_twiceSegmentWeight_of_chain
    (enter : CycleConnectorKind)
    (blocks : List (CycleConnectorKind × Bool))
    (hChain : blocks.IsChain OptionalKindFollow)
    (hFirst : ∀ a ∈ blocks.head?, OptionalKindFirst enter a) :
    twiceSegmentWeight enter (optionalKindWord blocks) =
      twiceSegmentWeight enter (blocks.map Prod.fst) :=
  OptionalKindValid.twiceSegmentWeight_preserved enter blocks
    (optionalKindValid_of_chain enter blocks hChain hFirst)

/-- Each optional block ends in its old connector. Thus the expanded
word and the old source connector list have exactly the same last entry. -/
theorem optionalKindWord_getLast?
    (blocks : List (CycleConnectorKind × Bool)) :
    (optionalKindWord blocks).getLast? =
      (blocks.map Prod.fst).getLast? := by
  induction blocks with
  | nil => rfl
  | cons hd tail ih =>
      rcases hd with ⟨kind, flag⟩
      cases tail with
      | nil =>
          cases flag <;> rfl
      | cons nxt rest =>
          rcases nxt with ⟨kind', flag'⟩
          cases flag <;> cases flag' <;>
            simpa [optionalKindWord] using ih

/-- The cyclic twice-weight of a connector-kind list, defined as
the opened walk with its final connector as entering boundary. -/
def cyclicKindTwiceWeight (word : List CycleConnectorKind) : ℕ :=
  match word.getLast? with
  | none => 0
  | some enter => twiceSegmentWeight enter word

/-- Optional insertion preserves the cyclic List weight under the
same chain-local hypotheses. This is still a List statement: identifying
it with the manuscript BigCycle.twiceOrder is the next obligation. -/
theorem optionalKindWord_cyclicWeight_preserved
    (blocks : List (CycleConnectorKind × Bool))
    (enter : CycleConnectorKind)
    (hLast : (blocks.map Prod.fst).getLast? = some enter)
    (hChain : blocks.IsChain OptionalKindFollow)
    (hFirst : ∀ a ∈ blocks.head?, OptionalKindFirst enter a) :
    cyclicKindTwiceWeight (optionalKindWord blocks) =
      cyclicKindTwiceWeight (blocks.map Prod.fst) := by
  simp only [cyclicKindTwiceWeight, optionalKindWord_getLast?, hLast]
  exact optionalKindWord_twiceSegmentWeight_of_chain
    enter blocks hChain hFirst

end StructuralRamsey.Girth

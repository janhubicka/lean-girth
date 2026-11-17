import Girth.ForestTraceLocalChordless
import Girth.FiniteTracePairGraph

/-!
# No bounded chordless cyclic pair pattern in a trace pair graph

This bridge translates the purely combinatorial obstruction from
ForestTraceLocalChordless into the pair graph of ORIGINAL traces.
A finite family of required graph edges is cyclic (every endpoint
belongs to a distinct required edge). For each two distinct
required edges, their four endpoints contain a nonedge.
Therefore one original bag cannot cover two required edges.
The bounded original-index local-completion hypothesis yields
a contradiction by the join-tree leaf-deletion argument.

For a standard induced cycle of length >= 4, taking its successive
edges supplies all these hypotheses. The separate map from
a Mathlib SimpleGraph cycle to these finite edge-indexed data
remains to be implemented.
-/

namespace StructuralRamsey.Girth

universe v w
variable {W ι : Type v} {E : Type w}

/-- An explicit chordlessness certificate for a pair of required
edges: the endpoints of the two edges include a distinct nonadjacent
pair in the original trace pair graph. -/
def CrossPairNonedge
    (G : SimpleGraph W) (a b : E → W)
    (e f : E) : Prop :=
  ∃ x y : W,
    x ≠ y ∧
    (x = a e ∨ x = b e ∨ x = a f ∨ x = b f) ∧
    (y = a e ∨ y = b e ∨ y = a f ∨ y = b f) ∧
    ¬ G.Adj x y

/-- The local completion property on original members excludes
all bounded cyclic edge systems having cross-pair nonedges.
The graph and its vertices are the actual trace graph on Z. -/
theorem no_bounded_chordless_pair_pattern
    [Fintype ι] [Fintype E] [Nonempty E]
    (F : ι → Set W) (Z : Set W) (q : ℕ)
    (hLocal : HasInternalJoinTreeCompletions F q)
    (a b : E → Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁)
    (hCard : Fintype.card E ≤ q)
    (hOtherA :
      ∀ e : E, ∃ f : E, f ≠ e ∧
        (a f = a e ∨ b f = a e))
    (hOtherB :
      ∀ e : E, ∃ f : E, f ≠ e ∧
        (a f = b e ∨ b f = b e))
    (hPairs :
      ∀ e : E, (tracePairGraph F Z).Adj (a e) (b e))
    (hCross :
      ∀ e f : E, e ≠ f →
        CrossPairNonedge (tracePairGraph F Z) a b e f) :
    False := by
  classical
  let aW : E → W := fun e => (a e).1
  let bW : E → W := fun e => (b e).1
  have hOtherAW :
      ∀ e : E, ∃ f : E, f ≠ e ∧
        (aW f = aW e ∨ bW f = aW e) := by
    intro e
    obtain ⟨f, hfe, hShare⟩ := hOtherA e
    refine ⟨f, hfe, ?_⟩
    rcases hShare with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hOtherBW :
      ∀ e : E, ∃ f : E, f ≠ e ∧
        (aW f = bW e ∨ bW f = bW e) := by
    intro e
    obtain ⟨f, hfe, hShare⟩ := hOtherB e
    refine ⟨f, hfe, ?_⟩
    rcases hShare with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hPairsW :
      ∀ e : E, ∃ i : ι,
        aW e ∈ F i ∧ bW e ∈ F i := by
    intro e
    obtain ⟨_, i, ha, hb⟩ := hPairs e
    exact ⟨i, ha, hb⟩
  have hUniqueW :
      ∀ i : ι, ∀ e f : E, e ≠ f →
        (aW e ∈ F i ∧ bW e ∈ F i) →
        (aW f ∈ F i ∧ bW f ∈ F i) → False := by
    intro i e f hef hePair hfPair
    obtain ⟨x, y, hxy, hx, hy, hNotAdj⟩ :=
      hCross e f hef
    have hEndpoint :
        ∀ z : Z,
          (z = a e ∨ z = b e ∨ z = a f ∨ z = b f) →
          z.1 ∈ F i := by
      intro z hz
      rcases hz with h | h | h | h
      · simpa only [h] using hePair.1
      · simpa only [h] using hePair.2
      · simpa only [h] using hfPair.1
      · simpa only [h] using hfPair.2
    have hAdj : (tracePairGraph F Z).Adj x y :=
      ⟨hxy, i, hEndpoint x hx, hEndpoint y hy⟩
    exact hNotAdj hAdj
  exact no_cyclic_unique_pairs_of_internal_completion
    F q hLocal aW bW e₀ e₁ he hCard
    hOtherAW hOtherBW hPairsW hUniqueW

end StructuralRamsey.Girth

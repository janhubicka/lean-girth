import Girth.Berge

/-!
# Exact pair-shadow condition for the edge-sensitive A2 clause

In a big cycle the A2 connector test asks whether two selected
vertex connectors admit ANY common ambient support edge. An edge
restriction can preserve wagon carriers while deleting that edge.
For an identified collection of connector-side pairs we isolate the
necessary one-sided witness retention hypothesis and prove the exact
equivalence of those edge-existence predicates.

No cycle syntax, wagon acceptability, or full system-Girth preservation
is assumed or concluded here.
-/

namespace StructuralRamsey.Girth

universe u
variable {V : Type u}

/-- The ambient hypergraph has an edge joining the two vertices. -/
def hasAmbientPairEdge (E : Set (Set V)) (x y : V) : Prop :=
  ∃ e : Set V, e ∈ E ∧ x ∈ e ∧ y ∈ e

/-- Every old edge witness for a specified connector-side vertex pair
has some (possibly different) surviving edge witness. -/
def A2PairShadowNoLoss
    (old new : Set (Set V)) (pairs : Set (V × V)) : Prop :=
  ∀ p ∈ pairs,
    hasAmbientPairEdge old p.1 p.2 →
      hasAmbientPairEdge new p.1 p.2

/-- An edge deletion cannot create a new pair-edge witness. -/
theorem hasAmbientPairEdge_mono
    {new old : Set (Set V)} (hSub : new ⊆ old)
    {x y : V} (h : hasAmbientPairEdge new x y) :
    hasAmbientPairEdge old x y := by
  rcases h with ⟨e, he, hx, hy⟩
  exact ⟨e, hSub he, hx, hy⟩

/-- The no-loss hypothesis is exactly the additional implication
needed to make pair-edge existence invariant under edge pruning. -/
theorem hasAmbientPairEdge_iff_on_of_A2_noLoss
    {old new : Set (Set V)} {pairs : Set (V × V)}
    (hSub : new ⊆ old)
    (hNoLoss : A2PairShadowNoLoss old new pairs)
    {x y : V} (hPair : (x, y) ∈ pairs) :
    hasAmbientPairEdge old x y ↔
      hasAmbientPairEdge new x y := by
  constructor
  · intro hOld
    exact hNoLoss (x, y) hPair hOld
  · exact hasAmbientPairEdge_mono hSub

/-- Therefore the A2 *absence* clause for every retained side pair
has exactly the same truth value before and after guarded pruning. -/
theorem A2_absence_iff_on_of_shadow_noLoss
    {old new : Set (Set V)} {pairs : Set (V × V)}
    (hSub : new ⊆ old)
    (hNoLoss : A2PairShadowNoLoss old new pairs)
    {x y : V} (hPair : (x, y) ∈ pairs) :
    (¬ hasAmbientPairEdge old x y) ↔
      (¬ hasAmbientPairEdge new x y) := by
  have hWitness :=
    hasAmbientPairEdge_iff_on_of_A2_noLoss
      hSub hNoLoss hPair
  constructor
  · intro hOld hNew
    exact hOld (hWitness.mpr hNew)
  · intro hNew hOld
    exact hNew (hWitness.mp hOld)

end StructuralRamsey.Girth

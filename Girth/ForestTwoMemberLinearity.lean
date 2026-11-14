import Girth.ForestMixedSetBound
import Girth.ForestCompletionSeparatorRequests
import Girth.ForestCarrierCorner
import Girth.Support

/-!
# Two-member mixed forests already force support linearity

The direct forest increment is invoked with q >= 2. Its old mixed
forest hypothesis includes every ambient A-edge as a tested one-edge
piece. Applying that hypothesis to two different one-edge members
shows that their carriers cannot share two vertices: the alternative
allowed intersection would force their genuine edges to coincide.

Thus old-picture A-linearity is not a new input to the direct
increment. This proof uses the faithful finite-SET mixed forest
predicate and never tries to lift a potentially duplicated list
to a forest.

Uncompiled Track 2 source candidate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {W : Type v}

/-- If every one-edge H-piece is tested and any two tested pieces
form a forest, then H is linear. Physical piece equality is
checked, rather than assuming arbitrary embeddings have different
supports. -/
theorem linearEdgeSet_of_finiteMixedForestThrough_oneEdges
    (H : Set (Set W)) (tested : HypergraphPiece W → Prop)
    (m : ℕ) (hm : 2 ≤ m)
    (hForest : FiniteMixedForestThrough tested m)
    (hTest : ∀ e : Set W, e ∈ H →
      tested (HypergraphPiece.oneEdge e)) :
    LinearEdgeSet H := by
  classical
  intro e f he hf hef
  let E : HypergraphPiece W := HypergraphPiece.oneEdge e
  let F : HypergraphPiece W := HypergraphPiece.oneEdge f
  have hEF : E ≠ F := by
    intro h
    apply hef
    have hCarrier := congrArg HypergraphPiece.carrier h
    simpa [E, F, HypergraphPiece.oneEdge] using hCarrier
  let s : Finset (HypergraphPiece W) := {E, F}
  have hTestS :
      ∀ T : HypergraphPiece W, T ∈ s → tested T := by
    intro T hT
    have hs : T = E ∨ T = F := by
      simpa only [s, Finset.mem_insert, Finset.mem_singleton] using hT
    rcases hs with hE | hF
    · subst T
      exact hTest e he
    · subst T
      exact hTest f hf
  have hCard : s.card ≤ m := by
    have hTwo : s.card ≤ 2 := by
      simp [s, hEF]
    exact hTwo.trans hm
  have hPair := (hForest s hTestS hCard).pairwiseAllowed
  let xe : {T : HypergraphPiece W // T ∈ s} :=
    ⟨E, by simp [s]⟩
  let xf : {T : HypergraphPiece W // T ∈ s} :=
    ⟨F, by simp [s]⟩
  have hDistinct : xe ≠ xf := by
    intro h
    exact hEF (congrArg Subtype.val h)
  rcases hPair hDistinct with hSmall | ⟨g, hgE, hgF, _hInter⟩
  · change (e ∩ f).Subsingleton at hSmall
    exact hSmall
  · have hgEqE : g = e := by
      change g ∈ ({e} : Set (Set W)) at hgE
      simpa using hgE
    have hgEqF : g = f := by
      change g ∈ ({f} : Set (Set W)) at hgF
      simpa using hgF
    exact (hef (hgEqE.symm.trans hgEqF)).elim

/-- Relational A-linearity follows from the old mixed two-member
forest condition, provided all actual ambient A-copies were tested.
No separate old A-linearity assumption is necessary. -/
theorem aLinear_of_finiteMixedForestThrough_oneEdges
    {L : RelLanguage.{u}} {UA X : Type v}
    (A : RelStructure L UA) (C : RelStructure L X)
    (tested : HypergraphPiece X → Prop)
    (m : ℕ) (hm : 2 ≤ m)
    (hForest : FiniteMixedForestThrough tested m)
    (hTestA : ∀ a : RelStructure.Embedding A C,
      tested (HypergraphPiece.oneEdge (copyCarrier a))) :
    ALinear A C := by
  have hSupportLinear :
      LinearEdgeSet (supportCopies A C) :=
    linearEdgeSet_of_finiteMixedForestThrough_oneEdges
      (supportCopies A C) tested m hm hForest
      (by
        intro e he
        obtain ⟨a, ha⟩ := he
        rw [ha]
        exact hTestA a)
  intro a b hDistinct
  exact hSupportLinear ⟨a, rfl⟩ ⟨b, rfl⟩ hDistinct

end StructuralRamsey.Girth

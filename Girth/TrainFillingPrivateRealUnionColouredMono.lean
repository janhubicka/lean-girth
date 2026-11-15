import Girth.TrainFillingPrivateRealUnionColoured
import Girth.TrainFillingColouredOrderedEdgePresentation

set_option Elab.async false

/-!
# Every actual coloured A-edge embedding into W is increasing

The ordered EHN theorem requires StrictMono for EVERY induced
A-embedding into the target W, not just the selected summand
inclusions. Since A is the genuine ordered ONE-EDGE structure,
the unary predicates and binary within-predicate order already
force every A-copy in each first wagon to preserve colours
and its internal order.

If the source one-edge colour profile and original global
vertex order list their predicate blocks consecutively,
these relations also determine the order between different
colours. This produces hLocalMono and hence EHN's hmono
for the actual dependent disjoint union W.

This does not assume any order on all closure embeddings in X:
only the EHN-selected increasing copies are subsequently kept.
Candidate source; exact-head Lean compilation remains required.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- A genuine coloured one-edge induced embedding into an
induced F_p preserves each vertex's unary colour, since
it must preserve the corresponding unary relation. -/
theorem colouredFirstWagonACopy_preservesColour
    {I : Type u} {V : Type v} [LinearOrder V]
    (k : ℕ) (profile : Fin k → I)
    (E : Set (Set V)) (colour : V → I) (S : Set V)
    (a : Embedding
      (colouredOrderedEdgeSource.{u,v} k profile)
      ((colouredOrderedEdgeTarget k E colour).induce S))
    (x : ULift.{v} (Fin k)) :
    colour (a x).1 = profile x.down := by
  have h := (a.map_rel_iff (.inl (.inr (profile x.down)))
    (fun _ : Fin 1 => x)).mpr (by
      change profile x.down = profile x.down
      rfl)
  change colour (a x).1 = profile x.down at h
  exact h

/-- Every A-embedding into a genuine induced first wagon is
strictly increasing. Same-colour comparisons come from the
binary order RELATION itself; different-colour comparisons
come from the common block order in the edge profile and
the old vertex set. No monotonicity hypothesis on a is made.

The source block property is exactly the ordered coloured
one-edge type used throughout the manuscript. -/
theorem colouredFirstWagonACopy_strictMono
    {I : Type u} {V : Type v}
    [LinearOrder I] [LinearOrder V]
    (k : ℕ) (profile : Fin k → I)
    (hProfileBlocks : ∀ i j : Fin k,
      i < j → profile i ≠ profile j → profile i < profile j)
    (E : Set (Set V)) (colour : V → I)
    (hVertexBlocks : ∀ x y : V,
      colour x < colour y → x < y)
    (S : Set V)
    (a : Embedding
      (colouredOrderedEdgeSource.{u,v} k profile)
      ((colouredOrderedEdgeTarget k E colour).induce S)) :
    StrictMono a := by
  intro x y hxy
  have hxColour :=
    colouredFirstWagonACopy_preservesColour k profile
      E colour S a x
  have hyColour :=
    colouredFirstWagonACopy_preservesColour k profile
      E colour S a y
  by_cases hSame : profile x.down = profile y.down
  · have hSource :
        (colouredOrderedEdgeSource.{u,v} k profile).rel
          (.inr ()) ![x, y] := by
      change profile x.down = profile y.down ∧
        x.down < y.down
      exact ⟨hSame, hxy⟩
    have hMap := (a.map_rel_iff (.inr ()) ![x, y]).mpr hSource
    change colour (a x).1 = colour (a y).1 ∧
      (a x).1 < (a y).1 at hMap
    exact hMap.2
  · have hDifferent :
        colour (a x).1 < colour (a y).1 := by
      rw [hxColour, hyColour]
      exact hProfileBlocks x.down y.down hxy hSame
    exact hVertexBlocks (a x).1 (a y).1 hDifferent

/-- Specialize to the ACTUAL tagged disjoint union W of
induced first wagons from one original coloured structure.
Now hmono of the ordered EHN theorem follows from original
coloured one-edge relations, with no independently assumed
monotone A-copy family.

The two old-vertex block compatibility conditions can both
be realized by the chosen predicate-block order of V,
without altering its within-colour relations. -/
theorem colouredFirstWagonUnion_allACopies_strictMono
    {I : Type u} {V P : Type v}
    [LinearOrder I] [LinearOrder P] [LinearOrder V]
    (k : ℕ) (hk : 2 ≤ k)
    (profile : Fin k → I)
    (hProfileBlocks : ∀ i j : Fin k,
      i < j → profile i ≠ profile j → profile i < profile j)
    (E : Set (Set V)) (colour : V → I)
    (oldCarrier : P → Set V)
    (hOldBlocks : ∀ x y : V,
      colour x ≠ colour y →
      x < y → colour x < colour y)
    (hOldColourToOrder : ∀ x y : V,
      colour x < colour y → x < y) :
    let D := colouredOrderedEdgeTarget k E colour
    let W := firstWagonDisjointUnion
      oldCarrier (fun p => D.induce (oldCarrier p))
    letI : LinearOrder (FirstWagonUnionVertex oldCarrier) :=
      firstWagonUnionOrder oldCarrier colour
    ∀ a : Embedding (colouredOrderedEdgeSource.{u,v} k profile) W,
      StrictMono a := by
  intro a
  let D := colouredOrderedEdgeTarget k E colour
  let local : (p : P) → RelStructure
      (colouredOrderedEdgeLanguage I k)
        {x : V // x ∈ oldCarrier p} :=
    fun p => D.induce (oldCarrier p)
  let hPositive := colouredOrderedEdgeLanguage_positive_arity k hk
  let hSpan := colouredOrderedEdgeSource_hasSpanningRelation k profile
  have hLocalMono : ∀ p : P, ∀ b :
      Embedding (colouredOrderedEdgeSource.{u,v} k profile)
        (local p), StrictMono b := by
    intro p b
    exact colouredFirstWagonACopy_strictMono k profile
      hProfileBlocks E colour hOldColourToOrder (oldCarrier p) b
  exact firstWagonDisjointUnion_allACopies_strictMono
    (colouredOrderedEdgeSource.{u,v} k profile)
      oldCarrier local hPositive hSpan
      colour hOldBlocks hLocalMono

end StructuralRamsey.Girth

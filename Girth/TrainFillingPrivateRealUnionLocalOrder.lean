import Girth.TrainFillingPrivateRealUnionColoured
import Girth.TrainFillingColouredBlockMonotone

set_option Elab.async false

/-!
# Actual coloured first-wagon A-copies are increasing

The genuine A-source is colouredOrderedEdgeSource k profile on
ULift(Fin k), with the unary predicate and within-colour
order relations. The ambient original D is literally
colouredOrderedEdgeTarget k E oldColour, with one GLOBAL
vertex order listing the predicate blocks consecutively.

For an induced local first wagon D.induce V(F_p), a relational
A-embedding preserves unary colours. Within the same colour
its relational order preservation gives increasing vertices.
Between different colours, the source profile's colour-block
order and the target D's colour-block order give the inequality.

Thus EVERY local A-embedding is globally StrictMono and
the hLocalMono input to the actual disjoint-union EHN
construction is derived, not separately postulated.

No arbitrariness of selected X order is used. The actual
W order is constructed independently by
TrainFillingPrivateRealUnionOrder.

This is a Lean source candidate until exact-head build.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- The source coloured one-edge type has all instances of
a single unary predicate and order relation. An embedding
into an ACTUAL old induced F_p preserves both exactly. -/
theorem colouredOriginalFirstWagon_ACopy_strictMono
    {I : Type v} {V : Type v}
    [LinearOrder I] [LinearOrder V]
    (k : ℕ) (sourceColour : Fin k → I)
    (oldEdges : Set (Set V)) (oldColour : V → I)
    (hSourceBlocks : ∀ i j : Fin k,
      i < j → sourceColour i ≠ sourceColour j →
        sourceColour i < sourceColour j)
    (hTargetBlocks : ∀ x y : V,
      oldColour x < oldColour y → x < y)
    (S : Set V)
    (a : Embedding
      (colouredOrderedEdgeSource (v := v) k sourceColour)
      ((colouredOrderedEdgeTarget k oldEdges oldColour).induce S)) :
    StrictMono a := by
  have hColour (u : ULift.{v} (Fin k)) :
      oldColour (a u).1 = sourceColour u.down := by
    have h := (a.map_rel_iff (.inl (.inr (sourceColour u.down)))
      (fun _ : Fin 1 => u)).mpr (by
        change sourceColour u.down = sourceColour u.down
        rfl)
    change oldColour (a u).1 = sourceColour u.down at h
    exact h
  intro x y hxy
  have hxyFin : x.down < y.down := hxy
  change (a x).1 < (a y).1
  by_cases hSame : sourceColour x.down = sourceColour y.down
  · have h := (a.map_rel_iff (.inr ()) ![x, y]).mpr (by
      change sourceColour x.down = sourceColour y.down ∧
        x.down < y.down
      exact ⟨hSame, hxyFin⟩)
    change oldColour (a x).1 = oldColour (a y).1 ∧
      (a x).1 < (a y).1 at h
    exact h.2
  · have hColours :
        sourceColour x.down < sourceColour y.down :=
      hSourceBlocks x.down y.down hxyFin hSame
    apply hTargetBlocks
    rw [hColour x, hColour y]
    exact hColours

/-- All A-embeddings in the ACTUAL disjoint union W are
globally increasing, provided the old original structure
D is ordered by unary-colour blocks and the source
one-edge type A uses the same block ordering.

No hmono hypothesis on W is given as an input: the
real relational one-edge structure and true summand
embeddings derive it through the spanning-edge theorem.
This is exactly the hmono condition of the ordered EHN
witness, not the stronger false assertion that arbitrary
closure embeddings of W into X are increasing. -/
theorem colouredRealFirstWagonUnion_allACopies_strictMono
    {I : Type v} {V P : Type v}
    [LinearOrder I] [LinearOrder V] [LinearOrder P]
    (k : ℕ) (hk : 2 ≤ k)
    (sourceColour : Fin k → I)
    (oldEdges : Set (Set V)) (oldColour : V → I)
    (hSourceBlocks : ∀ i j : Fin k,
      i < j → sourceColour i ≠ sourceColour j →
        sourceColour i < sourceColour j)
    (hOldColourBlocks : ∀ x y : V,
      oldColour x ≠ oldColour y →
      x < y → oldColour x < oldColour y)
    (hTargetBlocks : ∀ x y : V,
      oldColour x < oldColour y → x < y)
    (oldCarrier : P → Set V) :
    let D := colouredOrderedEdgeTarget k oldEdges oldColour
    let W := firstWagonDisjointUnion oldCarrier
      (fun p => D.induce (oldCarrier p))
    letI : LinearOrder (FirstWagonUnionVertex oldCarrier) :=
      firstWagonUnionOrder oldCarrier oldColour
    ∀ a : Embedding
        (colouredOrderedEdgeSource (v := v) k sourceColour) W,
      StrictMono a := by
  let D := colouredOrderedEdgeTarget k oldEdges oldColour
  let U := colouredOrderedEdgeSource (v := v) k sourceColour
  let local := fun p : P => D.induce (oldCarrier p)
  exact firstWagonDisjointUnion_allACopies_strictMono
    U oldCarrier local
      (colouredOrderedEdgeLanguage_positive_arity k hk)
      (colouredOrderedEdgeSource_hasSpanningRelation k sourceColour)
      oldColour hOldColourBlocks
      (fun p a =>
        colouredOriginalFirstWagon_ACopy_strictMono
          k sourceColour oldEdges oldColour
            hSourceBlocks hTargetBlocks (oldCarrier p) a)

end StructuralRamsey.Girth

import Girth.TrainFillingPrivateChoiceTaggedTarget
import Girth.TrainFillingIndexedColouredInsertionOrder
import Girth.TrainFillingColouredBlockMonotone

set_option Elab.async false

/-!
# The true selected original T vertices retain colours and orders

A source T-vertex v has literal tag
    tau_c(v) = ⟨c, Sum.inl v⟩
in the actual heterogenous contracted M.

The actual colour-first insertion order of M restricts to the
original old V order inside every selected c, provided old V is
itself ordered by predicate-colour blocks. Its unary colour is
literally oldColour v, not a separately chosen target colour.

For a genuine RELATIONAL embedding b of that actual coloured M
into a block-ordered coloured N, the checked
  colouredOrderedEmbedding_preserves_colour
and
  colouredOrderedEmbedding_strictMono
then prove the vertex map b ∘ tau_c preserves unary colours
and the entire original V order (hence all prescribed
within-predicate orders) for every selected component c.

This is independent of a separately assumed physical target
edge map and uses the SAME b as the two-arrow colour proof.
The remaining original T train relations are handled by
PrivateOriginalTrainInH, after actual parentwise realization.

Candidate source; no Lean kernel elaboration has been run.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {C V P X I Y : Type v}
variable (U : C → PrivateWagonInput V P X)
variable [LinearOrder C] [LinearOrder V] [Fintype V]
variable [LinearOrder P] [LinearOrder X] [LinearOrder I]

/-- A tagged original vertex keeps exactly its original unary
predicate colour, including shared old vertices of different
first wagons of the SAME selected choice. -/
theorem originalTargetVertex_colour
    (oldColour : V → I) (templateColour : X → I)
    (c : C) (v : V) :
    contractedVertexColour U oldColour templateColour
      (originalTargetVertexEmbedding U c v) = oldColour v := rfl

/-- The original T vertex order is retained inside each choice
component by the ACTUAL colouredChoiceInsertionOrder of M.
The hOldBlocks hypothesis is the permissible choice of
one colour-first global order extending the original orders
inside each predicate; no arbitrary order on M is assumed. -/
theorem originalTargetVertex_strictMono
    (oldColour : V → I) (templateColour : X → I)
    (hOldBlocks : ∀ a b : V,
      oldColour a ≠ oldColour b →
      a < b → oldColour a < oldColour b)
    (c : C) :
    letI : LinearOrder (Vertex U) :=
      colouredChoiceInsertionOrder U oldColour templateColour
    StrictMono (originalTargetVertexEmbedding U c) := by
  intro a b hab
  change colouredChoiceInsertionKey U oldColour templateColour
    (tagVertex U c (Sum.inl a)) <
    colouredChoiceInsertionKey U oldColour templateColour
      (tagVertex U c (Sum.inl b))
  by_cases hSame : oldColour a = oldColour b
  · have hKey : (U c).insertionKey (Sum.inl a) <
        (U c).insertionKey (Sum.inl b) :=
      (U c).insertionOrder_old_lt hab
    have hInner :
        (toLex (c, (U c).insertionKey (Sum.inl a)) :
          C ×ₗ (WithTop V ×ₗ WithTop (P ×ₗ X))) <
        toLex (c, (U c).insertionKey (Sum.inl b)) :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hKey⟩)
    exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨hSame, hInner⟩)
  · exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inl (hOldBlocks a b hSame hab))

/-- Every actual selected relational M-copy in an N whose
predicate blocks are ordered compatibly preserves the original
T vertices' unary colours, with NO extra colour condition
on the selected map j. -/
theorem selectedColouredM_originalTarget_colour
    [LinearOrder Y] {k : ℕ}
    (oldColour : V → I) (templateColour : X → I)
    (oldEdges : Set (Set Y)) (targetColour : Y → I)
    (b : Embedding (actualIndexedContractedM U oldColour templateColour)
      (colouredOrderedEdgeTarget k oldEdges targetColour))
    (c : C) (v : V) :
    targetColour (b (originalTargetVertexEmbedding U c v)) =
      oldColour v := by
  letI : LinearOrder (Vertex U) :=
    colouredChoiceInsertionOrder U oldColour templateColour
  have hColour :=
    colouredOrderedEmbedding_preserves_colour k
      (Set.range (contractedCarrier U)) oldEdges
      (contractedVertexColour U oldColour templateColour)
      targetColour b (originalTargetVertexEmbedding U c v)
  calc
    targetColour (b (originalTargetVertexEmbedding U c v)) =
        contractedVertexColour U oldColour templateColour
          (originalTargetVertexEmbedding U c v) := hColour
    _ = oldColour v := originalTargetVertex_colour U
      oldColour templateColour c v

/-- The SAME selected relational b used for the complete
colour-word arrow preserves the original T vertex order,
including all within-predicate orders, as soon as the target N
has its chosen predicate blocks in the common order.
No independent monotonicity assumption on j ∘ tau_c remains. -/
theorem selectedColouredM_originalTarget_strictMono
    [LinearOrder Y] {k : ℕ}
    (oldColour : V → I) (templateColour : X → I)
    (hOldBlocks : ∀ a b : V,
      oldColour a ≠ oldColour b →
      a < b → oldColour a < oldColour b)
    (oldEdges : Set (Set Y)) (targetColour : Y → I)
    (hTargetBlocks : ∀ x y : Y,
      targetColour x < targetColour y → x < y)
    (b : Embedding (actualIndexedContractedM U oldColour templateColour)
      (colouredOrderedEdgeTarget k oldEdges targetColour))
    (c : C) :
    StrictMono (fun v : V =>
      b (originalTargetVertexEmbedding U c v)) := by
  letI : LinearOrder (Vertex U) :=
    colouredChoiceInsertionOrder U oldColour templateColour
  have hSourceBlocks :
      ∀ x y : Vertex U,
        contractedVertexColour U oldColour templateColour x ≠
          contractedVertexColour U oldColour templateColour y →
        x < y →
          contractedVertexColour U oldColour templateColour x <
          contractedVertexColour U oldColour templateColour y := by
    intro x y hDifferent hxy
    change colouredChoiceInsertionKey U oldColour templateColour x <
      colouredChoiceInsertionKey U oldColour templateColour y at hxy
    rcases Prod.Lex.toLex_lt_toLex.mp hxy with hLess | ⟨hEqual, _⟩
    · exact hLess
    · exact False.elim (hDifferent hEqual)
  have hbMono : StrictMono b :=
    colouredOrderedEmbedding_strictMono k
      (Set.range (contractedCarrier U)) oldEdges
      (contractedVertexColour U oldColour templateColour)
      targetColour b hSourceBlocks hTargetBlocks
  have hTauMono : StrictMono (originalTargetVertexEmbedding U c) :=
    originalTargetVertex_strictMono U oldColour templateColour
      hOldBlocks c
  exact hbMono.comp hTauMono

end StructuralRamsey.Girth.IndexedPrivateChoice

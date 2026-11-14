import Girth.TrainFillingIndexedColouredInsertionOrder

set_option Elab.async false

/-!
# Sorting the EHN template order by predicate colours

The ordered EHN input equips X with a total auxiliary order, but the
actual contracted-coloured M requires the X order to have its
predicate-colour classes as consecutive ordered blocks.

Reorder X lexicographically: first the predicate colour, then its
ORIGINAL EHN auxiliary order. This preserves the auxiliary order
WITHIN each colour and makes hXBlocks automatic. A selected
colour-preserving W-copy that was globally monotone for the
original EHN order remains monotone in the new block order,
provided the SOURCE W was already block ordered.

The proof uses no EHN/Ramsey theorem and is a reusable
finite-order preparation lemma. It is a new Lean proof candidate
until compiled on the exact repository head.
-/

namespace StructuralRamsey.Girth

universe v

/-- First sort by the predicate colour, then by the pre-existing
order within that colour. The key is injective even if distinct
vertices have the same colour. -/
noncomputable def colourBlockOrder
    {I X : Type v} [LinearOrder I] [LinearOrder X]
    (colour : X → I) : LinearOrder X :=
  LinearOrder.lift'
    (fun x : X => (toLex (colour x, x) : I ×ₗ X))
    (by
      intro x y h
      exact congrArg (fun k : I ×ₗ X => (ofLex k).2) h)

/-- The new order lists different predicate colours in the
prescribed increasing colour order. -/
theorem colourBlockOrder_of_colour_lt
    {I X : Type v} [LinearOrder I] [LinearOrder X]
    (colour : X → I) {x y : X}
    (hxy : colour x < colour y) :
    @LT.lt X (colourBlockOrder colour).toLT x y := by
  change (toLex (colour x, x) : I ×ₗ X) <
      (toLex (colour y, y) : I ×ₗ X)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hxy)

/-- Equal-colour vertices retain their original relative order. -/
theorem colourBlockOrder_of_same_colour
    {I X : Type v} [LinearOrder I] [LinearOrder X]
    (colour : X → I) {x y : X}
    (hColour : colour x = colour y) (hxy : x < y) :
    @LT.lt X (colourBlockOrder colour).toLT x y := by
  change (toLex (colour x, x) : I ×ₗ X) <
      (toLex (colour y, y) : I ×ₗ X)
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨hColour, hxy⟩)

/-- Strictly increasing positions in different predicate blocks
must have increasing predicate colours (the hXBlocks condition
of the genuine coloured heterogeneous M support theorem). -/
theorem colourBlockOrder_blocks
    {I X : Type v} [LinearOrder I] [LinearOrder X]
    (colour : X → I) (x y : X)
    (hDifferent : colour x ≠ colour y)
    (hxy : @LT.lt X (colourBlockOrder colour).toLT x y) :
    colour x < colour y := by
  change (toLex (colour x, x) : I ×ₗ X) <
      (toLex (colour y, y) : I ×ₗ X) at hxy
  rcases Prod.Lex.toLex_lt_toLex.mp hxy with hLt | ⟨hEq, _⟩
  · exact hLt
  · exact False.elim (hDifferent hEq)

/-- Reblocking the target by colour does not spoil an originally
increasing colour-preserving embedding of a source whose global
order already consists of the same consecutive colour blocks.

The source order stays unchanged. The target order after the
local letI is the explicitly constructed colourBlockOrder. -/
theorem strictMono_into_colourBlockOrder
    {I W X : Type v}
    [LinearOrder I] [LinearOrder W] [LinearOrder X]
    (colourW : W → I) (colourX : X → I)
    (f : W → X)
    (hPreserve : ∀ x : W, colourX (f x) = colourW x)
    (hMono : StrictMono f)
    (hWBlocks : ∀ x y : W,
      colourW x ≠ colourW y → x < y → colourW x < colourW y) :
    letI : LinearOrder X := colourBlockOrder colourX
    StrictMono f := by
  change ∀ x y : W, x < y →
    @LT.lt X (colourBlockOrder colourX).toLT (f x) (f y)
  intro x y hxy
  by_cases hSame : colourW x = colourW y
  · have hTargetColour : colourX (f x) = colourX (f y) := by
      rw [hPreserve x, hPreserve y]
      exact hSame
    exact colourBlockOrder_of_same_colour colourX hTargetColour
      (hMono hxy)
  · have hColours : colourX (f x) < colourX (f y) := by
      rw [hPreserve x, hPreserve y]
      exact hWBlocks x y hSame hxy
    exact colourBlockOrder_of_colour_lt colourX hColours


/-- Sorting BOTH source and target by their predicate colours
preserves an old strictly increasing colour-preserving map,
without asking that the old source order had any block property.
This permits the disjoint union W and EHN template X to be put
in compatible coloured block orders using the same witness. -/
theorem strictMono_between_colourBlockOrders
    {I W X : Type v}
    [LinearOrder I] [LinearOrder W] [LinearOrder X]
    (colourW : W → I) (colourX : X → I) (f : W → X)
    (hPreserve : ∀ x : W, colourX (f x) = colourW x)
    (hMono : StrictMono f) :
    letI : LinearOrder W := colourBlockOrder colourW
    letI : LinearOrder X := colourBlockOrder colourX
    StrictMono f := by
  change ∀ x y : W,
    @LT.lt W (colourBlockOrder colourW).toLT x y →
      @LT.lt X (colourBlockOrder colourX).toLT (f x) (f y)
  intro x y hxy
  have hKeys :
      (toLex (colourW x, x) : I ×ₗ W) <
        (toLex (colourW y, y) : I ×ₗ W) := hxy
  rcases Prod.Lex.toLex_lt_toLex.mp hKeys with hDifferent | ⟨hSame, hOld⟩
  · apply colourBlockOrder_of_colour_lt colourX
    rw [hPreserve x, hPreserve y]
    exact hDifferent
  · apply colourBlockOrder_of_same_colour colourX
    · rw [hPreserve x, hPreserve y]
      exact hSame
    · exact hMono hOld

end StructuralRamsey.Girth

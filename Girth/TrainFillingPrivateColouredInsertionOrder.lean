import Girth.TrainFillingPrivateGlobalInsertionOrder

set_option Elab.async false

/-!
# Compatible global orders respecting the prescribed colour blocks

The verified finite anchor construction and the candidate global
insertion-key order compare old and private vertices correctly within
each entire first wagon. But the global insertion order need NOT
concatenate the unary colour predicates in the required order:
a private vertex with no old successor is inserted at the top.

We correct this by sorting first by the actual unary colour, then by
the global insertion key. If the old coordinate maps preserve colours
and their full X order, and X and V use the same colour-block
convention, this order simultaneously (1) places every lower-colour
vertex before every higher-colour vertex, (2) preserves old V order,
and (3) makes every complete first-wagon X-placement strictly
monotone. No output order is postulated.

This is a choicewise order on PrivateWagonInput.Vertex; the full
heterogeneous union over all choices uses one further choice-tagged
lexicographic order, preserving the same block comparisons.
-/

namespace StructuralRamsey.Girth.PrivateWagonInput

universe v
variable {V P X I : Type v}
variable (U : PrivateWagonInput V P X)
variable [LinearOrder V] [Fintype V] [LinearOrder P]
variable [LinearOrder X] [LinearOrder I]

/-- The genuine unary colour of every old or private position. -/
def privateColour (oldColour : V → I) (templateColour : X → I) :
    U.Vertex → I
  | .inl v => oldColour v
  | .inr z => templateColour z.1.2

/-- A real old-coordinate colour restriction forces every complete
X-placement, including its added private points, to preserve colours. -/
theorem privateColour_place
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ p : P, ∀ z : {v : V // v ∈ U.oldCarrier p},
      oldColour z.1 = templateColour (U.coordinate p z))
    (p : P) (x : X) :
    U.privateColour oldColour templateColour (U.place p x) =
      templateColour x := by
  classical
  by_cases h : x ∈ Set.range (U.coordinate p)
  · obtain ⟨z, hz⟩ := h
    have hp : U.place p x = Sum.inl z.1 := by
      rw [← hz]
      exact U.place_old p z
    rw [hp]
    change oldColour z.1 = templateColour x
    exact (hColour p z).trans (congrArg templateColour hz)
  · have hp : U.place p x =
        Sum.inr (⟨(p, x), h⟩ : U.PrivateVertex) := by
      simp only [PrivateWagonInput.place, dif_neg h]
    rw [hp]
    rfl

/-- The colour-first lex key prevents a private position of a low
colour with anchor top from appearing after a higher-colour old point. -/
noncomputable def colouredInsertionKey
    (oldColour : V → I) (templateColour : X → I) :
    U.Vertex → I ×ₗ (WithTop V ×ₗ WithTop (P ×ₗ X)) :=
  fun z => toLex (U.privateColour oldColour templateColour z,
    U.insertionKey z)

/-- Colour sorting adds no identification: the insertion key is
already injective on every actual old and private vertex. -/
theorem colouredInsertionKey_injective
    (oldColour : V → I) (templateColour : X → I) :
    Function.Injective
      (U.colouredInsertionKey oldColour templateColour) := by
  intro a b h
  apply U.insertionKey_injective
  exact congrArg
    (fun z : I ×ₗ (WithTop V ×ₗ WithTop (P ×ₗ X)) =>
      (ofLex z).2) h

/-- One canonical common-order constructor for a whole expanded choice,
with the colour-block order built in. -/
noncomputable def colouredInsertionOrder
    (oldColour : V → I) (templateColour : X → I) :
    LinearOrder U.Vertex :=
  LinearOrder.lift' (U.colouredInsertionKey oldColour templateColour)
    (U.colouredInsertionKey_injective oldColour templateColour)

/-- Different colour blocks occur in the stipulated order,
independently of first-wagon ownership and insertion anchors. -/
theorem colouredInsertionOrder_block_lt
    (oldColour : V → I) (templateColour : X → I)
    (a b : U.Vertex)
    (hab : U.privateColour oldColour templateColour a <
      U.privateColour oldColour templateColour b) :
    @LT.lt U.Vertex (U.colouredInsertionOrder oldColour templateColour).toLT
      a b := by
  change U.colouredInsertionKey oldColour templateColour a <
    U.colouredInsertionKey oldColour templateColour b
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hab)

/-- The chosen coloured order retains the old V order, assuming the
original old order also concatenates the common colour blocks. -/
theorem colouredInsertionOrder_old_lt
    (oldColour : V → I) (templateColour : X → I)
    (hOldBlocks : ∀ a b : V, oldColour a ≠ oldColour b →
      a < b → oldColour a < oldColour b)
    {a b : V} (hab : a < b) :
    @LT.lt U.Vertex (U.colouredInsertionOrder oldColour templateColour).toLT
      (Sum.inl a) (Sum.inl b) := by
  change U.colouredInsertionKey oldColour templateColour (Sum.inl a) <
    U.colouredInsertionKey oldColour templateColour (Sum.inl b)
  by_cases hSame : oldColour a = oldColour b
  · exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨hSame, U.insertionOrder_old_lt hab⟩)
  · exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inl (hOldBlocks a b hSame hab))

/-- EVERY complete first-wagon X-placement is increasing for this
single colour-first total order. Intra-colour comparisons use the
verified insertion key inequalities; inter-colour comparisons are
determined by the stipulated common colour-block order on X. -/
theorem colouredInsertionOrder_place_lt
    (oldColour : V → I) (templateColour : X → I)
    (hColour : ∀ p : P, ∀ z : {v : V // v ∈ U.oldCarrier p},
      oldColour z.1 = templateColour (U.coordinate p z))
    (hCoordinate : ∀ p : P, StrictMono (U.coordinate p))
    (hTemplateBlocks : ∀ x y : X,
      templateColour x ≠ templateColour y →
      x < y → templateColour x < templateColour y)
    (p : P) {x y : X} (hxy : x < y) :
    @LT.lt U.Vertex (U.colouredInsertionOrder oldColour templateColour).toLT
      (U.place p x) (U.place p y) := by
  change U.colouredInsertionKey oldColour templateColour (U.place p x) <
    U.colouredInsertionKey oldColour templateColour (U.place p y)
  have hCx := U.privateColour_place oldColour templateColour hColour p x
  have hCy := U.privateColour_place oldColour templateColour hColour p y
  by_cases hSame : templateColour x = templateColour y
  · exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨by simpa only [hCx, hCy] using hSame,
        U.insertionOrder_place_lt hCoordinate p hxy⟩)
  · have hColourLt := hTemplateBlocks x y hSame hxy
    exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inl (by simpa only [hCx, hCy] using hColourLt))

end StructuralRamsey.Girth.PrivateWagonInput

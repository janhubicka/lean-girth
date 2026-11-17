import Girth.TrainFillingPrivateRealDisjointUnion

set_option Elab.async false

/-!
# One predicate-block order on the actual unequal first-wagon union W

Given the genuine tagged disjoint-union vertex type
  Sigma p, {v : V // v ∈ F_p},
order first by the original unary predicate colour, then by
the first-wagon tag p, then by the original old vertex order.

The lexicographic key is injective, so this is ONE global
LinearOrder on W. Its restriction to every original F_p is
strictly increasing if the old V order is colour-block ordered.
Its unary colour function is literally the original colour
of v, and all W colour blocks occur consecutively.

Thus the concrete inclusion F_p -> W constructed by
TrainFillingPrivateRealDisjointUnion is automatically
strictly monotone, instead of an independently postulated
hIncludeMono in the ordered EHN summand construction.
The chosen order does not identify different copies of
a shared original vertex across distinct first wagons.

Source-only proof candidates until exact-head Lean compilation.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {P V : Type v} {I : Type u}
variable [LinearOrder P] [LinearOrder V] [LinearOrder I]

/-- The actual unary colour of a vertex of the tagged union.
A shared vertex occurring in F_p and F_q has two distinct W
representatives, but both retain the same unary colour. -/
def firstWagonUnionColour
    (oldCarrier : P → Set V) (oldColour : V → I) :
    FirstWagonUnionVertex oldCarrier → I :=
  fun z => oldColour z.2.1

/-- Concrete lexicographic key: predicate colour, then
first-wagon owner, then original old vertex. -/
def firstWagonUnionOrderKey
    (oldCarrier : P → Set V) (oldColour : V → I) :
    FirstWagonUnionVertex oldCarrier → I ×ₗ (P ×ₗ V) :=
  fun z => toLex (oldColour z.2.1, toLex (z.1, z.2.1))

/-- Distinct tagged old vertices have distinct keys. In
particular, equal V-values in different F_p remain distinct. -/
theorem firstWagonUnionOrderKey_injective
    (oldCarrier : P → Set V) (oldColour : V → I) :
    Function.Injective (firstWagonUnionOrderKey oldCarrier oldColour) := by
  rintro ⟨p, x⟩ ⟨q, y⟩ h
  have hpq : p = q :=
    congrArg
      (fun k : I ×ₗ (P ×ₗ V) => (ofLex (ofLex k).2).1) h
  have hxy : x.1 = y.1 :=
    congrArg
      (fun k : I ×ₗ (P ×ₗ V) => (ofLex (ofLex k).2).2) h
  subst q
  have heq : x = y := Subtype.ext hxy
  cases heq
  rfl

/-- The full ordered disjoint union W with predicate-colour
blocks first, and the prescribed original order within
each component's predicate class. -/
noncomputable def firstWagonUnionOrder
    (oldCarrier : P → Set V) (oldColour : V → I) :
    LinearOrder (FirstWagonUnionVertex oldCarrier) :=
  LinearOrder.lift'
    (firstWagonUnionOrderKey oldCarrier oldColour)
    (firstWagonUnionOrderKey_injective oldCarrier oldColour)

/-- All distinct colour blocks of W are in the stipulated
order, independently of the first-wagon tags. -/
theorem firstWagonUnionOrder_blocks
    (oldCarrier : P → Set V) (oldColour : V → I)
    (a b : FirstWagonUnionVertex oldCarrier)
    (hDifferent :
      firstWagonUnionColour oldCarrier oldColour a ≠
      firstWagonUnionColour oldCarrier oldColour b)
    (hab : @LT.lt (FirstWagonUnionVertex oldCarrier)
      (firstWagonUnionOrder oldCarrier oldColour).toLT a b) :
    firstWagonUnionColour oldCarrier oldColour a <
      firstWagonUnionColour oldCarrier oldColour b := by
  change firstWagonUnionOrderKey oldCarrier oldColour a <
    firstWagonUnionOrderKey oldCarrier oldColour b at hab
  rcases Prod.Lex.toLex_lt_toLex.mp hab with hColour | ⟨hSame, _⟩
  · exact hColour
  · exact False.elim (hDifferent hSame)

/-- Each genuine original component inclusion F_p -> W is
strictly increasing for the FULL selected EHN source order,
provided old T was already block ordered by unary colours.
No arbitrary global coordinate map or extra target order
is assumed in this result. -/
theorem firstWagonSummandEmbedding_strictMono
    (oldCarrier : P → Set V)
    (localStructure : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (oldColour : V → I)
    (hOldBlocks : ∀ x y : V,
      oldColour x ≠ oldColour y →
      x < y → oldColour x < oldColour y)
    (p : P) :
    letI : LinearOrder (FirstWagonUnionVertex oldCarrier) :=
      firstWagonUnionOrder oldCarrier oldColour
    StrictMono (firstWagonSummandEmbedding oldCarrier localStructure hPositive p) := by
  change ∀ x y : {x : V // x ∈ oldCarrier p}, x < y →
      firstWagonUnionOrderKey oldCarrier oldColour
        ⟨p, x⟩ < firstWagonUnionOrderKey oldCarrier oldColour ⟨p, y⟩
  intro x y hxy
  have hxyVal : x.1 < y.1 := hxy
  by_cases hSame : oldColour x.1 = oldColour y.1
  · have hInner :
        (toLex (p, x.1) : P ×ₗ V) <
          toLex (p, y.1) :=
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl, hxyVal⟩)
    exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨hSame, hInner⟩)
  · exact Prod.Lex.toLex_lt_toLex.mpr
      (Or.inl (hOldBlocks x.1 y.1 hSame hxyVal))

/-- Original unary colours of local vertices are preserved
literally by inclusion in the genuine ordered W, with no
extra predicate-colour map assigned on the union. -/
theorem firstWagonSummandEmbedding_colour
    (oldCarrier : P → Set V)
    (localStructure : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (oldColour : V → I) (p : P)
    (x : {x : V // x ∈ oldCarrier p}) :
    firstWagonUnionColour oldCarrier oldColour
      (firstWagonSummandEmbedding oldCarrier localStructure hPositive p x) =
      oldColour x.1 := rfl


/-- If every original A-copy in each F_p is increasing and
the actual component inclusions are increasing, then EVERY
A-copy in the genuine tagged W is increasing. The spanning
A-edge ensures that it lies in one component, where the
original local monotonicity applies.

This is exactly the hmono input of ordered EHN. It is NOT
a claim that every future closed X-copy is monotone:
those are restricted separately to the selected family. -/
theorem firstWagonDisjointUnion_allACopies_strictMono
    {UA : Type v} [LinearOrder UA]
    (A : RelStructure L UA)
    (oldCarrier : P → Set V)
    (localStructure : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (hSpan : HasSpanningRelation A)
    (oldColour : V → I)
    (hOldBlocks : ∀ x y : V,
      oldColour x ≠ oldColour y →
      x < y → oldColour x < oldColour y)
    (hLocalMono : ∀ p : P, ∀ a : Embedding A (localStructure p),
      StrictMono a) :
    letI : LinearOrder (FirstWagonUnionVertex oldCarrier) :=
      firstWagonUnionOrder oldCarrier oldColour
    ∀ a : Embedding A (firstWagonDisjointUnion oldCarrier localStructure),
      StrictMono a := by
  letI : LinearOrder (FirstWagonUnionVertex oldCarrier) :=
    firstWagonUnionOrder oldCarrier oldColour
  intro a
  obtain ⟨p, hInside⟩ :=
    firstWagonUnion_Acopy_in_one_summand A oldCarrier localStructure
      hPositive hSpan a
  let inc := firstWagonSummandEmbedding oldCarrier localStructure hPositive p
  have hFactor : ∀ x : UA,
      ∃ y : {x : V // x ∈ oldCarrier p}, a x = inc y := by
    intro x
    obtain ⟨y, hy⟩ := hInside ⟨x, rfl⟩
    exact ⟨y, hy.symm⟩
  let b : Embedding A (localStructure p) :=
    a.factorThroughRange inc hFactor
  have hEq : inc.comp b = a := by
    apply Embedding.ext
    intro x
    exact (Classical.choose_spec (hFactor x)).symm
  have hInc : StrictMono inc :=
    firstWagonSummandEmbedding_strictMono oldCarrier localStructure
      hPositive oldColour hOldBlocks p
  have hComposed : StrictMono (inc.comp b) :=
    hInc.comp (hLocalMono p b)
  rw [hEq] at hComposed
  exact hComposed

end StructuralRamsey.Girth

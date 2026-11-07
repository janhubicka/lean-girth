import Girth.TrainFillingPrivateInsertionAnchors
import Mathlib.Order.Prod.Lex.Basic

set_option Elab.async false

/-!
# A single compatible private first-wagon order

The old vertices V retain their global linear order. Each private
vertex is identified by its owner p and X-position x. Its insertion
anchor is the least old p-vertex after x in the local X-order (or
top when there is none).

We compare (anchor, tie-breaker) lexicographically. An old vertex v
has key (v, top), while a private (p,x) has key (anchor(p,x),(p,x)).
Thus private positions with anchor v precede old v; private positions
of the same first wagon retain the X-order at equal anchors.

The construction is genuinely global: no independently chosen local
or output order is assumed. Correct order of each entire first-wagon
placement follows from the previously checked anchor inequalities and
strict monotonicity of the genuine old coordinate injections.
-/

namespace StructuralRamsey.Girth.PrivateWagonInput

universe v
variable {V P X : Type v}
variable (U : PrivateWagonInput V P X)
variable [LinearOrder V] [Fintype V] [LinearOrder P] [LinearOrder X]

/-- The global lexicographic insertion key on every old/private vertex. -/
noncomputable def insertionKey :
    U.Vertex → WithTop V ×ₗ WithTop (P ×ₗ X)
  | .inl v =>
      toLex ((v : WithTop V), (⊤ : WithTop (P ×ₗ X)))
  | .inr z =>
      toLex
        (U.insertionAnchor z.1.1 z.1.2,
          ((toLex z.1 : P ×ₗ X) : WithTop (P ×ₗ X)))

/-- Distinct old vertices and actual private positions have distinct keys;
in particular no added label is identified with an old vertex. -/
theorem insertionKey_injective : Function.Injective (U.insertionKey) := by
  intro a b h
  cases a with
  | inl v =>
      cases b with
      | inl w =>
          have hFirst : (v : WithTop V) = (w : WithTop V) :=
            congrArg
              (fun z : WithTop V ×ₗ WithTop (P ×ₗ X) => (ofLex z).1) h
          exact congrArg Sum.inl (WithTop.coe_injective hFirst)
      | inr z =>
          have hSecond : (⊤ : WithTop (P ×ₗ X)) =
              ((toLex z.1 : P ×ₗ X) : WithTop (P ×ₗ X)) :=
            congrArg
              (fun z : WithTop V ×ₗ WithTop (P ×ₗ X) => (ofLex z).2) h
          cases hSecond
  | inr z =>
      cases b with
      | inl w =>
          have hSecond :
              ((toLex z.1 : P ×ₗ X) : WithTop (P ×ₗ X)) =
                (⊤ : WithTop (P ×ₗ X)) :=
            congrArg
              (fun z : WithTop V ×ₗ WithTop (P ×ₗ X) => (ofLex z).2) h
          cases hSecond
      | inr w =>
          have hSecond :
              ((toLex z.1 : P ×ₗ X) : WithTop (P ×ₗ X)) =
                ((toLex w.1 : P ×ₗ X) : WithTop (P ×ₗ X)) :=
            congrArg
              (fun z : WithTop V ×ₗ WithTop (P ×ₗ X) => (ofLex z).2) h
          have hPair : z.1 = w.1 :=
            congrArg ofLex (WithTop.coe_injective hSecond)
          exact congrArg Sum.inr (Subtype.ext hPair)

/-- One total order on the FULL actual private-extension vertex set. -/
noncomputable def insertionOrder : LinearOrder U.Vertex :=
  LinearOrder.lift' U.insertionKey U.insertionKey_injective

/-- This global order keeps the original old vertex order exactly. -/
theorem insertionOrder_old_lt {a b : V} (hab : a < b) :
    @LT.lt U.Vertex (U.insertionOrder).toLT
      (Sum.inl a) (Sum.inl b) := by
  change U.insertionKey (Sum.inl a) <
    U.insertionKey (Sum.inl b)
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inl (WithTop.coe_lt_coe.mpr hab))

/-- Every entire local X-placement is strictly increasing in ONE
global order, provided the original old first-wagon coordinates are
strictly increasing in their prescribed source/target orders. -/
theorem insertionOrder_place_lt
    (hCoordinate : ∀ p : P, StrictMono (U.coordinate p))
    (p : P) {x y : X} (hxy : x < y) :
    @LT.lt U.Vertex (U.insertionOrder).toLT
      (U.place p x) (U.place p y) := by
  classical
  change U.insertionKey (U.place p x) <
    U.insertionKey (U.place p y)
  by_cases hx : x ∈ Set.range (U.coordinate p)
  · obtain ⟨a, ha⟩ := hx
    have hxp : U.place p x = Sum.inl a.1 := by
      rw [← ha]
      exact U.place_old p a
    by_cases hy : y ∈ Set.range (U.coordinate p)
    · obtain ⟨b, hb⟩ := hy
      have hyp : U.place p y = Sum.inl b.1 := by
        rw [← hb]
        exact U.place_old p b
      rw [hxp, hyp]
      have hab : a.1 < b.1 := by
        have hlt : U.coordinate p a < U.coordinate p b := by
          simpa only [ha, hb] using hxy
        exact (hCoordinate p).lt_iff_lt.mp hlt
      exact Prod.Lex.toLex_lt_toLex.mpr
        (Or.inl (WithTop.coe_lt_coe.mpr hab))
    · have hyp : U.place p y =
          Sum.inr (⟨(p, y), hy⟩ : U.PrivateVertex) := by
        simp only [PrivateWagonInput.place, dif_neg hy]
      rw [hxp, hyp]
      have hAnchor : (a.1 : WithTop V) <
          U.insertionAnchor p y :=
        U.old_lt_insertionAnchor hCoordinate p a y
          (by simpa only [ha] using hxy)
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hAnchor)
  · have hxp : U.place p x =
        Sum.inr (⟨(p, x), hx⟩ : U.PrivateVertex) := by
      simp only [PrivateWagonInput.place, dif_neg hx]
    by_cases hy : y ∈ Set.range (U.coordinate p)
    · obtain ⟨b, hb⟩ := hy
      have hyp : U.place p y = Sum.inl b.1 := by
        rw [← hb]
        exact U.place_old p b
      rw [hxp, hyp]
      have hAnchor : U.insertionAnchor p x ≤ (b.1 : WithTop V) :=
        U.insertionAnchor_le_old p x b
          (by simpa only [hb] using hxy)
      rcases lt_or_eq_of_le hAnchor with hlt | heq
      · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
      · exact Prod.Lex.toLex_lt_toLex.mpr
          (Or.inr ⟨heq, WithTop.coe_lt_top _⟩)
    · have hyp : U.place p y =
          Sum.inr (⟨(p, y), hy⟩ : U.PrivateVertex) := by
        simp only [PrivateWagonInput.place, dif_neg hy]
      rw [hxp, hyp]
      have hAnchor : U.insertionAnchor p x ≤
          U.insertionAnchor p y :=
        U.insertionAnchor_mono p hxy.le
      rcases lt_or_eq_of_le hAnchor with hlt | heq
      · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
      · have hTie : (toLex (p, x) : P ×ₗ X) <
            (toLex (p, y) : P ×ₗ X) :=
          Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hxy⟩)
        exact Prod.Lex.toLex_lt_toLex.mpr
          (Or.inr ⟨heq, WithTop.coe_lt_coe.mpr hTie⟩)

end StructuralRamsey.Girth.PrivateWagonInput

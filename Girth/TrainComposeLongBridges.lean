import Girth.TrainOutputA1Length
import Girth.TrainFreshWagonA2

/-!
# Circulation: composing two short bridges into a genuine long piece

During a second supreme collapse, an inserted long piece
  e⁺ W f⁺
is replaced by a short edge through its left boundary and W, and
another short edge through W and its right boundary.

These two actual edges are in W. They are necessarily DISTINCT:
if they were equal, that edge would join the two ORIGINAL boundary
vertices, contradicting the nonedge clause of the first LongValid
piece. Consequently they form a genuine new LongValid piece for the
original occurrence, with the same two source boundaries.

This is the local geometric composition statement missing from the
circulation admissible-replacement lemma. It does not claim the
global second-cycle indexing, a composed PlanValid for every occurrence,
or automatic acceptability of an arbitrary expanded cycle.

No output-wagon linearity, global cycle transfer, or appendix result.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Two actual edge bridges through one wagon compose to a legal
long piece when no ambient edge joins their outside vertices. -/
theorem longPiece_of_two_bridges
    (a : I ⊕ E) (x y : V) (w : P)
    (hx : D.Bridge a x w) (hy : D.Bridge a y w)
    (hNoPair : ¬ D.PairEdge x y) :
    D.LongPiece a (.inl x) (.inl y) := by
  obtain ⟨e, he, hew, hxe⟩ := hx
  obtain ⟨f, hf, hfw, hyf⟩ := hy
  have hef : e ≠ f := by
    intro h
    apply hNoPair
    exact ⟨e, hxe, h ▸ hyf⟩
  exact ⟨x, y, w, e, f, rfl, rfl, he, hf, hef,
    hew, hfw, hxe, hyf, hNoPair⟩

/-- The two MIXED short pieces appearing in a later collapse
recombine to a genuine source long piece across their common wagon.
The short pieces are not merely carrier-intersection claims: they
supply actual source edges and physical wagon incidence. -/
theorem longPiece_of_two_mixed_shorts
    (a : I ⊕ E) (x y : V) (w : P)
    (hl : D.ShortPiece a (.inl x) (.inr w))
    (hr : D.ShortPiece a (.inr w) (.inl y))
    (hNoPair : ¬ D.PairEdge x y) :
    D.LongPiece a (.inl x) (.inl y) := by
  have hb1 : D.Bridge a x w :=
    D.piece_mixed_bridge a x w (Or.inl hl)
  have hb2 : D.Bridge a y w :=
    D.piece_mixed_bridge_reverse a y w (Or.inl hr)
  exact D.longPiece_of_two_bridges a x y w hb1 hb2 hNoPair

/-- Genuine bridges for the original boundary pair yield ACTUAL
LongValid physical edges in any target source occurrence. -/
theorem BigCycle.exists_longValid_of_two_bridges
    {n : ℕ} (C : D.BigCycle n) (k j : Fin n)
    (x y : V) (w : P)
    (hPrev : C.connector (trainCyclicPred j) = Sum.inl x)
    (hHere : C.connector j = Sum.inl y)
    (hb1 : D.Bridge (C.label k) x w)
    (hb2 : D.Bridge (C.label k) y w)
    (hNoPair : ¬ D.PairEdge x y) :
    ∃ e f : E, C.LongValid D k j e w f := by
  obtain ⟨e, he, hew, hxe⟩ := hb1
  obtain ⟨f, hf, hfw, hyf⟩ := hb2
  have hef : e ≠ f := by
    intro h
    apply hNoPair
    exact ⟨e, hxe, h ▸ hyf⟩
  exact ⟨e, f, x, y, hPrev, hHere, he, hf, hef,
    hew, hfw, hxe, hyf, hNoPair⟩

/-- LOCAL composition of a previous long piece and two later bridges:
the previous piece supplies the two original boundary vertices and
their nonedge condition; the second collapse supplies target-copy
bridges to the SAME inserted wagon. No output-cycle legality needed. -/
theorem BigCycle.compose_longValid_of_bridges
    {n : ℕ} (C : D.BigCycle n) (kOld kNew j : Fin n)
    (e f : E) (w : P)
    (hOld : C.LongValid D kOld j e w f)
    (hBridges : ∀ (x y : V),
      C.connector (trainCyclicPred j) = Sum.inl x →
      C.connector j = Sum.inl y →
      D.Bridge (C.label kNew) x w ∧
      D.Bridge (C.label kNew) y w) :
    ∃ g h : E, C.LongValid D kNew j g w h := by
  obtain ⟨x, y, hPrev, hHere, _he, _hf, _hne,
    _hew, _hfw, _hxe, _hyf, hNoPair⟩ := hOld
  obtain ⟨hb1, hb2⟩ := hBridges x y hPrev hHere
  exact C.exists_longValid_of_two_bridges D kNew j x y w
    hPrev hHere hb1 hb2 hNoPair

end StructuralRamsey.Girth.OrderOneData

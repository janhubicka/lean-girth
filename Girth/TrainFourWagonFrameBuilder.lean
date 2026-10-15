import Girth.TrainFourOccurrenceWagonCycle

/-!
# Circulation: construct the four-occurrence frame from actual wagons

The four-occurrence cycle certificate retains two adjacent-label
inequalities beyond the original a != b and the genuine long-piece
edge inequality e != f. They need NOT be extra picture-step
assumptions: if b is the inserted physical edge e, its meeting
the old block wagon p forces parent(e)=p, whereas the long piece
puts e in a distinct wagon q. Likewise for the f/a boundary.

This lemma packages that easy but necessary argument as a constructor
for FourWagonFrame. Consequently the geometric picture-step proof
only has to establish original block incidence, one real long piece,
and distinct wagon connectors; both cross-label inequalities follow.

No appendix or broader cycle-transfer claim is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- If an actual edge label meets a wagon, its parent is that wagon.
The disjoint sum prevents confusion with designated copies even when
they have the same physical carrier. -/
theorem parent_eq_of_edge_label_meets
    (e : E) (p : P) (h : D.Meets (.inr e) p) :
    D.parent e = p := by
  rcases h with ⟨g, hg, hp⟩
  have hge : g = e := by
    simpa [OrderOneData.edges] using hg
  subst g
  exact hp

/-- Build the legal two-wagon four-occurrence frame from source
block data and a genuine long piece. No separate hypotheses
asserting b != e+ or f+ != a are necessary. -/
theorem FourWagonFrame.of_distinct_wagons
    (a b : I ⊕ E) (e f : E) (p q : P) (x y : V)
    (hab : a ≠ b) (hef : e ≠ f)
    (hpq : p ≠ q) (hxy : x ≠ y)
    (haMeets : D.Meets a p) (hbMeets : D.Meets b p)
    (hbX : x ∈ D.carrier b)
    (heX : x ∈ D.edgeCarrier e)
    (heQ : D.parent e = q)
    (hfQ : D.parent f = q)
    (hfY : y ∈ D.edgeCarrier f)
    (haY : y ∈ D.carrier a) :
    D.FourWagonFrame := by
  have hbe : b ≠ (Sum.inr e : I ⊕ E) := by
    intro hEq
    have hm : D.Meets (.inr e) p := by
      simpa [hEq] using hbMeets
    have hparent := D.parent_eq_of_edge_label_meets e p hm
    exact hpq (hparent.symm.trans heQ)
  have hfa : (Sum.inr f : I ⊕ E) ≠ a := by
    intro hEq
    have hm : D.Meets (.inr f) p := by
      simpa [← hEq] using haMeets
    have hparent := D.parent_eq_of_edge_label_meets f p hm
    exact hpq (hparent.symm.trans hfQ)
  exact {
    a := a
    b := b
    e := e
    f := f
    p := p
    q := q
    x := x
    y := y
    hab := hab
    hbe := hbe
    hef := hef
    hfa := hfa
    hpq := hpq
    hxy := hxy
    haMeets := haMeets
    hbMeets := hbMeets
    hbX := hbX
    heX := heX
    heQ := heQ
    hfQ := hfQ
    hfY := hfY
    haY := haY
  }

end StructuralRamsey.Girth.OrderOneData

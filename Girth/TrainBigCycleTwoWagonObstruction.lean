import Girth.TrainBigCycleOrderOneExtraction

/-!
# Circulation: two designated copies cannot meet two different wagons

This formalizes Lemma "Bridge edges and common wagons", part (ii),
using the genuine two-occurrence big-cycle syntax, A1--A3, and
the necessary local pieces of any supreme copy.

Two different designated labels meeting two distinct wagons create
a length-two, order-two acceptable cycle with two wagon connectors.
A short replacement would need one edge in both wagon classes;
a long replacement has only vertex endpoints. Neither is possible.

The statement is about the circulation proof, not an appendix.
-/

namespace StructuralRamsey.Girth
namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A legal short or long replacement with two wagon boundaries forces
the two wagon labels to coincide. In a genuine big cycle they do not. -/
theorem piece_two_wagon_forces_eq
    (a : I ⊕ E) (p q : P)
    (h : D.ShortPiece a (Sum.inr p) (Sum.inr q) ∨
      D.LongPiece a (Sum.inr p) (Sum.inr q)) : p = q := by
  rcases h with ⟨e, _he, hp, hq⟩ | h
  · obtain ⟨f, hf, hfp⟩ := hp
    obtain ⟨g, hg, hgq⟩ := hq
    have hfe : f = e := hf
    have hge : g = e := hg
    subst f
    subst g
    exact hfp.symm.trans hgq
  · rcases h with ⟨x, y, w, e, f, hq, _⟩
    cases hq

/-- The A W B X cycle, whose two connector kinds are both wagon. -/
def twoWagonBigCycle
    (a b : I) (p q : P) (hab : a ≠ b) (hpq : p ≠ q)
    (hap : D.Meets (.inl a) p)
    (haq : D.Meets (.inl a) q)
    (hbp : D.Meets (.inl b) p)
    (hbq : D.Meets (.inl b) q) :
    D.BigCycle 2 where
  length_ge_two := by omega
  label := ![Sum.inl a, Sum.inl b]
  connector := ![Sum.inr p, Sum.inr q]
  adjacent_ne := by
    intro i
    fin_cases i
    · simpa [cyclicSucc] using (fun h : (Sum.inl a : I ⊕ E) =
        Sum.inl b => hab (Sum.inl.inj h))
    · simpa [cyclicSucc] using (fun h : (Sum.inl b : I ⊕ E) =
        Sum.inl a => hab (Sum.inl.inj h).symm)
  connector_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all
  left_incident := by
    intro i
    fin_cases i
    · simpa [Incident] using hap
    · simpa [Incident] using hbq
  right_incident := by
    intro i
    fin_cases i
    · simpa [Incident, cyclicSucc] using hbp
    · simpa [Incident, cyclicSucc] using haq

/-- Both occurrences are pure, hence the big-cycle order is two. -/
theorem twoWagonBigCycle_twiceOrder
    (a b : I) (p q : P) (hab : a ≠ b) (hpq : p ≠ q)
    (hap : D.Meets (.inl a) p)
    (haq : D.Meets (.inl a) q)
    (hbp : D.Meets (.inl b) p)
    (hbq : D.Meets (.inl b) q) :
    (D.twoWagonBigCycle a b p q hab hpq hap haq hbp hbq).twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, connectorKind, twoWagonBigCycle,
    Fin.sum_univ_two, cyclicSucc, twiceOccurrenceWeight]

/-- The two-wagon cycle is acceptable: A1 is vacuous at order two,
and both A2 and A3 hold automatically at length two. -/
theorem twoWagonBigCycle_acceptable
    (a b : I) (p q : P) (hab : a ≠ b) (hpq : p ≠ q)
    (hap : D.Meets (.inl a) p)
    (haq : D.Meets (.inl a) q)
    (hbp : D.Meets (.inl b) p)
    (hbq : D.Meets (.inl b) q) :
    (D.twoWagonBigCycle a b p q hab hpq hap haq hbp hbq).Acceptable := by
  let C := D.twoWagonBigCycle a b p q hab hpq hap haq hbp hbq
  refine ⟨?_, D.twoCycle_A2 C, D.twoCycle_A3 C⟩
  intro ht
  have hfour : C.twiceOrder = 4 :=
    D.twoWagonBigCycle_twiceOrder a b p q hab hpq hap haq hbp hbq
  have heq : (4 : ℕ) = 2 := hfour.symm.trans ht
  exact False.elim ((by decide : (4 : ℕ) ≠ 2) heq)

/-- No selected label in this cycle can supply a legal replacement
for the opposite occurrence. This already refutes local supremeness. -/
theorem twoWagonBigCycle_no_localSupreme
    (a b : I) (p q : P) (hab : a ≠ b) (hpq : p ≠ q)
    (hap : D.Meets (.inl a) p)
    (haq : D.Meets (.inl a) q)
    (hbp : D.Meets (.inl b) p)
    (hbq : D.Meets (.inl b) q) :
    ¬ (D.twoWagonBigCycle a b p q hab hpq hap haq hbp hbq).HasLocalSupreme := by
  let C := D.twoWagonBigCycle a b p q hab hpq hap haq hbp hbq
  intro h
  rcases h with ⟨i, _hi, hp⟩
  fin_cases i
  · have hne : C.label 1 ≠ C.label 0 := by
      intro eq
      have hEq : (Sum.inl a : I ⊕ E) = Sum.inl b := by
        simpa [C, twoWagonBigCycle] using eq.symm
      exact hab (Sum.inl.inj hEq)
    have hpiece := hp 1 hne
    have heq : p = q :=
      D.piece_two_wagon_forces_eq (.inl a) p q
        (by simpa [C, twoWagonBigCycle, trainCyclicPred] using hpiece)
    exact hpq heq
  · have hne : C.label 0 ≠ C.label 1 := by
      intro eq
      have hEq : (Sum.inl a : I ⊕ E) = Sum.inl b := by
        simpa [C, twoWagonBigCycle] using eq
      exact hab (Sum.inl.inj hEq)
    have hpiece := hp 0 hne
    have heq : q = p :=
      D.piece_two_wagon_forces_eq (.inl b) q p
        (by simpa [C, twoWagonBigCycle, trainCyclicPred] using hpiece)
    exact hpq heq.symm

/-- The circulation's second bridge lemma follows from the order-two
necessary local consequence of full system-girth, without any
successor-tree argument or appendix input. -/
theorem no_two_designated_meet_two_wagons
    (h : D.LocalPieceSystemBound 2)
    (a b : I) (p q : P) (hab : a ≠ b) (hpq : p ≠ q)
    (hap : D.Meets (.inl a) p)
    (haq : D.Meets (.inl a) q)
    (hbp : D.Meets (.inl b) p)
    (hbq : D.Meets (.inl b) q) : False := by
  let C := D.twoWagonBigCycle a b p q hab hpq hap haq hbp hbq
  have hOrder : C.twiceOrder ≤ 2 * 2 := by
    rw [D.twoWagonBigCycle_twiceOrder a b p q hab hpq hap haq hbp hbq]
  have hSupreme : C.HasLocalSupreme :=
    h 2 C (D.twoWagonBigCycle_acceptable a b p q hab hpq hap haq hbp hbq)
      hOrder
  exact D.twoWagonBigCycle_no_localSupreme a b p q hab hpq hap haq hbp hbq hSupreme

end OrderOneData
end StructuralRamsey.Girth

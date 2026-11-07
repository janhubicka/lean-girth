import Girth.TrainTwoCopyCommonWagon
import Girth.TrainFullGirthCopyStrongness
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: both actual two-standard no-pair targets have LONG pieces

Consider a genuine two-occurrence reduced witness BigCycle with two
distinct designated standard labels i,j, distinct vertex connectors
x,y, and no ambient physical support edge through both x and y.

Under FullSystemGirthGT q at q >= 2, the already proved
two-copy local symmetry and common-long-wagon theorem yield
two distinct support edges in EACH standard, all in one and the
SAME genuine witness wagon w, with appropriate x/y contacts.

We specialize those pieces to the ACTUAL indexed reduced BigCycle:
target 0 has a LongValid piece at cut 1; target 1 has a reversed
LongValid piece at cut 0, using the other standard's edges in
the opposite order. Both use the SAME wagon w, not existential
unrelated wagon labels. No guessed original B-label identity,
no source owner run, and no fabricated physical edge.

This does not yet construct the original source long insertion,
or the two-step old-wagon short replacement. The actual source
contact dichotomy and transfer interfaces live in separate
circulation-only modules; no appendix or manuscript edits.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- For a genuine two-standard, two-vertex reduced BigCycle with no
physical pair edge, witness full girth makes a common real wagon and
actual LongValid pieces available at BOTH designated target indices.
Both pieces are correctly oriented to the literal Z.connector word. -/
theorem BigCycle.two_standard_no_pair_long_at_both_targets
    (Z : D.BigCycle 2)
    (q : ℕ) (hq : 2 ≤ q) (hFull : D.FullSystemGirthGT q)
    (i j : I)
    (hLabel0 : Z.label 0 = Sum.inl i)
    (hLabel1 : Z.label 1 = Sum.inl j)
    (x y : V)
    (hConnector0 : Z.connector 0 = Sum.inl x)
    (hConnector1 : Z.connector 1 = Sum.inl y)
    (hNoPair : ¬ D.PairEdge x y) :
    ∃ w : P,
      (∃ a b : E, Z.LongValid D (0 : Fin 2) (1 : Fin 2) a w b) ∧
      (∃ c d : E, Z.LongValid D (1 : Fin 2) (0 : Fin 2) c w d) := by
  have hxy : x ≠ y := by
    intro heq
    have hSame : Z.connector (0 : Fin 2) =
        Z.connector (1 : Fin 2) := by
      calc
        Z.connector 0 = Sum.inl x := hConnector0
        _ = Sum.inl y := by rw [heq]
        _ = Z.connector 1 := hConnector1.symm
    exact (by decide : (0 : Fin 2) ≠ 1)
      (Z.connector_injective hSame)
  have hij : i ≠ j := by
    intro heq
    have hSame : Z.label (0 : Fin 2) = Z.label (1 : Fin 2) := by
      calc
        Z.label 0 = Sum.inl i := hLabel0
        _ = Sum.inl j := by rw [heq]
        _ = Z.label 1 := hLabel1.symm
    exact (Z.adjacent_ne 0) (by simpa [cyclicSucc] using hSame)
  have hix : x ∈ D.copyCarrier i := by
    have h := Z.left_incident (0 : Fin 2)
    simpa [Incident, carrier, hLabel0, hConnector0] using h
  have hjx : x ∈ D.copyCarrier j := by
    have h := Z.right_incident (0 : Fin 2)
    simpa [Incident, carrier, hLabel1, hConnector0, cyclicSucc] using h
  have hiy : y ∈ D.copyCarrier i := by
    have h := Z.right_incident (1 : Fin 2)
    simpa [Incident, carrier, hLabel0, hConnector1, cyclicSucc] using h
  have hjy : y ∈ D.copyCarrier j := by
    have h := Z.left_incident (1 : Fin 2)
    simpa [Incident, carrier, hLabel1, hConnector1] using h
  have hLocal : D.LocalPieceSystemBound 2 := by
    intro n C hAccept hOrder
    exact D.localPieceSystemBound_of_supremeCycleBound q hFull.2
      n C hAccept (hOrder.trans (Nat.mul_le_mul_left 2 hq))
  obtain ⟨w, ⟨a, b, ha, hb, hab, hAw, hBw, hAx, hBy⟩,
    ⟨c, d, hc, hd, hcd, hCw, hDw, hCx, hDy⟩⟩ :=
    D.twoVertexTwoCopyCycle_common_long_wagon
      hFull.1 hLocal i j x y hij hxy
      hix hiy hjx hjy hNoPair
  have hNoPairYX : ¬ D.PairEdge y x := by
    rintro ⟨edge, hy, hx⟩
    exact hNoPair ⟨edge, hx, hy⟩
  have hLong0 : Z.LongValid D (0 : Fin 2) (1 : Fin 2)
      a w b := by
    refine ⟨x, y, ?_, hConnector1, ?_, ?_,
      hab, hAw, hBw, hAx, hBy, hNoPair⟩
    · simpa [trainCyclicPred] using hConnector0
    · simpa [hLabel0, edges] using ha
    · simpa [hLabel0, edges] using hb
  have hLong1 : Z.LongValid D (1 : Fin 2) (0 : Fin 2)
      d w c := by
    refine ⟨y, x, ?_, hConnector0, ?_, ?_,
      hcd.symm, hDw, hCw, hDy, hCx, hNoPairYX⟩
    · simpa [trainCyclicPred] using hConnector1
    · simpa [hLabel1, edges] using hd
    · simpa [hLabel1, edges] using hc
  exact ⟨w, ⟨a, b, hLong0⟩, ⟨d, c, hLong1⟩⟩


/-- The exact two-standard common-wagon symmetry stated on an
arbitrary indexed cut type Fin c with c=2. For EVERY possible
cut, the OTHER reduced standard has a genuine LongValid using
the SAME wagon w. This avoids identifying the canonical cut's
original index with a guessed 0 or 1 in the attached picture. -/
theorem BigCycle.two_standard_no_pair_long_each_cut_of_two
    {c : ℕ} (hc : c = 2)
    (Z : D.BigCycle c)
    (q : ℕ) (hq : 2 ≤ q) (hFull : D.FullSystemGirthGT q)
    (i j : I)
    (hLabel0 : Z.label ⟨0, by omega⟩ = Sum.inl i)
    (hLabel1 : Z.label ⟨1, by omega⟩ = Sum.inl j)
    (x y : V)
    (hConnector0 : Z.connector ⟨0, by omega⟩ = Sum.inl x)
    (hConnector1 : Z.connector ⟨1, by omega⟩ = Sum.inl y)
    (hNoPair : ¬ D.PairEdge x y) :
    ∃ w : P, ∀ cut : Fin c,
      ∃ a b : E, Z.LongValid D (trainCyclicPred cut) cut a w b := by
  subst c
  obtain ⟨w, hFirst, hSecond⟩ :=
    BigCycle.two_standard_no_pair_long_at_both_targets
      D Z q hq hFull i j hLabel0 hLabel1
      x y hConnector0 hConnector1 hNoPair
  refine ⟨w, ?_⟩
  intro cut
  fin_cases cut
  · simpa [trainCyclicPred] using hSecond
  · simpa [trainCyclicPred] using hFirst

end StructuralRamsey.Girth.OrderOneData

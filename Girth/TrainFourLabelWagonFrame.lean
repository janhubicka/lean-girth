import Girth.TrainBigCycleOrderOneExtraction

set_option Elab.async false

/-!
# Four arbitrary labels with alternating wagon and vertex connectors

The literal word a p b y c q d x has order two. Only adjacent labels must
differ; either diagonal pair may have equal labels. A2 follows from the
ambient no-pair guard. A3 has a separate exact hypothesis: every wagon
containing both x and y must be one of the connector wagons p,q. In
particular it follows when no wagon contains both vertices.

A locally supreme occurrence supplies a mixed bridge for the adjacent
occurrence across its vertex boundary. The resulting four alternatives
are occurrence-specific. They do not identify an output parent attached
to a repeated label, and they assert no simultaneous global replacement.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Four occurrences, retaining only the adjacent-label inequalities.
The diagonal labels a,c or b,d are allowed to coincide. -/
structure FourLabelWagonFrame (D : OrderOneData V E I P) where
  a : I ⊕ E
  b : I ⊕ E
  c : I ⊕ E
  d : I ⊕ E
  p : P
  q : P
  x : V
  y : V
  hab : a ≠ b
  hbc : b ≠ c
  hcd : c ≠ d
  hda : d ≠ a
  hpq : p ≠ q
  hxy : x ≠ y
  haMeets : D.Meets a p
  hbMeets : D.Meets b p
  hcMeets : D.Meets c q
  hdMeets : D.Meets d q
  haX : x ∈ D.carrier a
  hbY : y ∈ D.carrier b
  hcY : y ∈ D.carrier c
  hdX : x ∈ D.carrier d

/-- The literal alternating word a p b y c q d x. -/
def FourLabelWagonFrame.toBigCycle (F : D.FourLabelWagonFrame) : D.BigCycle 4 where
  length_ge_two := by omega
  label := ![F.a, F.b, F.c, F.d]
  connector := ![Sum.inr F.p, Sum.inl F.y, Sum.inr F.q, Sum.inl F.x]
  adjacent_ne := by
    intro k
    fin_cases k
    · simpa [cyclicSucc] using F.hab
    · simpa [cyclicSucc] using F.hbc
    · simpa [cyclicSucc] using F.hcd
    · simpa [cyclicSucc] using F.hda
  connector_injective := by
    intro k l h
    have hpq := F.hpq
    have hxy := F.hxy
    fin_cases k <;> fin_cases l <;> simp_all
  left_incident := by
    intro k
    fin_cases k
    · exact F.haMeets
    · exact F.hbY
    · exact F.hcMeets
    · exact F.hdX
  right_incident := by
    intro k
    fin_cases k
    · exact F.hbMeets
    · exact F.hcY
    · exact F.hdMeets
    · exact F.haX

/-- Every occurrence has one vertex and one wagon boundary, so the
four-occurrence frame has order two. -/
theorem FourLabelWagonFrame.twiceOrder_eq_four
    (F : D.FourLabelWagonFrame) : F.toBigCycle.twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, connectorKind, FourLabelWagonFrame.toBigCycle,
    Fin.sum_univ_four, cyclicSucc, twiceOccurrenceWeight]

/-- The alternating positions satisfy A2's location condition, and its
extra condition is the genuine ambient no-pair guard. -/
theorem FourLabelWagonFrame.A2_of_no_pair
    (F : D.FourLabelWagonFrame) (hNoPair : ¬ D.PairEdge F.x F.y) :
    F.toBigCycle.A2 := by
  have hNoReverse : ¬ D.PairEdge F.y F.x := by
    rintro ⟨e, hye, hxe⟩
    exact hNoPair ⟨e, hxe, hye⟩
  constructor
  · intro k w hw j hj
    fin_cases k <;> fin_cases j <;>
      simp_all [BigCycle.InWagonAt, FourLabelWagonFrame.toBigCycle,
        trainCyclicPred, cyclicSucc]
  · intro k w x y hw hPrev hNext _ _ _
    fin_cases k <;>
      simp_all [FourLabelWagonFrame.toBigCycle, trainCyclicPred, cyclicSucc]

/-- A3 requires that a nonconnector wagon not contain both opposite vertex
positions. No ambient nonedge statement alone is substituted for this premise. -/
theorem FourLabelWagonFrame.A3_of_common_wagons
    (F : D.FourLabelWagonFrame)
    (hCommon : ∀ r : P, D.WagonVertex r F.x → D.WagonVertex r F.y →
      r = F.p ∨ r = F.q) : F.toBigCycle.A3 := by
  intro r hr
  have hrp : r ≠ F.p := by
    intro h
    apply hr (0 : Fin 4)
    simp [FourLabelWagonFrame.toBigCycle, h]
  have hrq : r ≠ F.q := by
    intro h
    apply hr (2 : Fin 4)
    simp [FourLabelWagonFrame.toBigCycle, h]
  have hNotBoth : ¬ (D.WagonVertex r F.x ∧ D.WagonVertex r F.y) := by
    rintro ⟨hx, hy⟩
    exact (hCommon r hx hy).elim hrp hrq
  by_cases hx : D.WagonVertex r F.x
  · have hy : ¬ D.WagonVertex r F.y := fun hy => hNotBoth ⟨hx, hy⟩
    refine ⟨(2 : Fin 4), ?_⟩
    intro j hj
    fin_cases j <;>
      simp_all [BigCycle.InWagonAt, FourLabelWagonFrame.toBigCycle, cyclicSucc]
  · refine ⟨(0 : Fin 4), ?_⟩
    intro j hj
    fin_cases j <;>
      simp_all [BigCycle.InWagonAt, FourLabelWagonFrame.toBigCycle, cyclicSucc]

/-- Exact acceptability of the arbitrary-label frame, with separate A2 and
A3 premises. Neither all-label distinctness nor wagon linearity is assumed. -/
theorem FourLabelWagonFrame.acceptable
    (F : D.FourLabelWagonFrame) (hNoPair : ¬ D.PairEdge F.x F.y)
    (hCommon : ∀ r : P, D.WagonVertex r F.x → D.WagonVertex r F.y →
      r = F.p ∨ r = F.q) : F.toBigCycle.Acceptable := by
  refine ⟨?_, F.A2_of_no_pair D hNoPair, F.A3_of_common_wagons D hCommon⟩
  intro hOrder
  have hFour : F.toBigCycle.twiceOrder = 4 := F.twiceOrder_eq_four D
  omega

/-- A locally supreme occurrence supplies a bridge for the adjacent
occurrence across its vertex boundary. The four alternatives retain the
supreme OCCURRENCE; diagonal repeated labels need no global parent map. -/
theorem FourLabelWagonFrame.bridges_of_local_bound
    (F : D.FourLabelWagonFrame) (hBound : D.LocalPieceSystemBound 2)
    (hNoPair : ¬ D.PairEdge F.x F.y)
    (hCommon : ∀ r : P, D.WagonVertex r F.x → D.WagonVertex r F.y →
      r = F.p ∨ r = F.q) :
    (D.designated F.a ∧ D.Bridge F.a F.x F.q) ∨
      (D.designated F.b ∧ D.Bridge F.b F.y F.q) ∨
      (D.designated F.c ∧ D.Bridge F.c F.y F.p) ∨
      (D.designated F.d ∧ D.Bridge F.d F.x F.p) := by
  have hOrd : F.toBigCycle.twiceOrder ≤ 2 * 2 := by
    rw [F.twiceOrder_eq_four D]
  obtain ⟨k, hk, hPieces⟩ := hBound 4 F.toBigCycle
    (F.acceptable D hNoPair hCommon) hOrd
  fin_cases k
  · have hne : F.toBigCycle.label 3 ≠ F.toBigCycle.label 0 := F.hda
    have hPiece := hPieces 3 hne
    refine Or.inl ⟨hk, ?_⟩
    exact D.piece_mixed_bridge_reverse F.a F.x F.q
      (by simpa [FourLabelWagonFrame.toBigCycle, trainCyclicPred] using hPiece)
  · have hne : F.toBigCycle.label 2 ≠ F.toBigCycle.label 1 := F.hbc.symm
    have hPiece := hPieces 2 hne
    refine Or.inr (Or.inl ⟨hk, ?_⟩)
    exact D.piece_mixed_bridge F.b F.y F.q
      (by simpa [FourLabelWagonFrame.toBigCycle, trainCyclicPred] using hPiece)
  · have hne : F.toBigCycle.label 1 ≠ F.toBigCycle.label 2 := F.hbc
    have hPiece := hPieces 1 hne
    refine Or.inr (Or.inr (Or.inl ⟨hk, ?_⟩))
    exact D.piece_mixed_bridge_reverse F.c F.y F.p
      (by simpa [FourLabelWagonFrame.toBigCycle, trainCyclicPred] using hPiece)
  · have hne : F.toBigCycle.label 0 ≠ F.toBigCycle.label 3 := F.hda.symm
    have hPiece := hPieces 0 hne
    refine Or.inr (Or.inr (Or.inr ⟨hk, ?_⟩))
    exact D.piece_mixed_bridge F.d F.x F.p
      (by simpa [FourLabelWagonFrame.toBigCycle, trainCyclicPred] using hPiece)

end StructuralRamsey.Girth.OrderOneData

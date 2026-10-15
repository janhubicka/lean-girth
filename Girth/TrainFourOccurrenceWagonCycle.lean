import Girth.TrainSupremeVertexCoverage
import Girth.TrainBigCycleOrderBudget

/-!
# Circulation: the four-occurrence, two-wagon cycle

The unrestricted two-standard-copy obstruction uses a four-occurrence
cycle F₁ W₁ F₂ x e⁺ X f⁺ y inside ONE old standard picture.
Here F₁,F₂ may be designated labels, not just physical edges.

Formalize the exact finite object and isolate its acceptability:
* all four connectors are genuinely distinct;
* every occurrence has one vertex and one wagon boundary (order two);
* the A2 location condition is automatic for the alternating word;
* its A2 non-edge clause comes from the absence of any ambient x,y edge;
* A3 comes from uniqueness of the old wagon through the distinct
  vertices x,y, both of which lie in X.

Under system-Girth >2, an acceptable cycle has a genuinely supreme
designated copy. Its global replacement plan forces both x,y into
that copy, provided source edges lie in the carrier of their copy.
The final reduction to an H-edge then uses the boundary-intersection
observation separately; that geometric statement is not assumed here.
No appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Literal data for the four-occurrence configuration. This stores
the genuine adjacent-label inequalities rather than identifying
labels merely because their physical carriers differ. -/
structure FourWagonFrame (D : OrderOneData V E I P) where
  a : I ⊕ E
  b : I ⊕ E
  e : E
  f : E
  p : P
  q : P
  x : V
  y : V
  hab : a ≠ b
  hbe : b ≠ (Sum.inr e : I ⊕ E)
  hef : e ≠ f
  hfa : (Sum.inr f : I ⊕ E) ≠ a
  hpq : p ≠ q
  hxy : x ≠ y
  haMeets : D.Meets a p
  hbMeets : D.Meets b p
  hbX : x ∈ D.carrier b
  heX : x ∈ D.edgeCarrier e
  heQ : D.parent e = q
  hfQ : D.parent f = q
  hfY : y ∈ D.edgeCarrier f
  haY : y ∈ D.carrier a

/-- The literal cyclic word a p b x e⁺ q f⁺ y.
No classification of a or b as designated/actual is imposed. -/
def FourWagonFrame.toBigCycle (F : D.FourWagonFrame) :
    D.BigCycle 4 where
  length_ge_two := by omega
  label := ![F.a, F.b, Sum.inr F.e, Sum.inr F.f]
  connector := ![Sum.inr F.p, Sum.inl F.x, Sum.inr F.q, Sum.inl F.y]
  adjacent_ne := by
    intro k
    fin_cases k
    · simpa [cyclicSucc] using F.hab
    · simpa [cyclicSucc] using F.hbe
    · simpa [cyclicSucc] using
        (fun h : (Sum.inr F.e : I ⊕ E) = Sum.inr F.f =>
          F.hef (Sum.inr.inj h))
    · simpa [cyclicSucc] using F.hfa
  connector_injective := by
    intro k l hkl
    have hpq := F.hpq
    have hxy := F.hxy
    fin_cases k <;> fin_cases l <;>
      simp_all [cyclicSucc]
  left_incident := by
    intro k
    fin_cases k
    · simpa [Incident] using F.haMeets
    · simpa [Incident] using F.hbX
    · exact ⟨F.e, rfl, F.heQ⟩
    · exact F.hfY
  right_incident := by
    intro k
    fin_cases k
    · simpa [cyclicSucc, Incident] using F.hbMeets
    · simpa [cyclicSucc, Incident, carrier] using F.heX
    · simpa [cyclicSucc, Incident] using
        (show D.Meets (Sum.inr F.f) F.q from ⟨F.f, rfl, F.hfQ⟩)
    · simpa [cyclicSucc, Incident] using F.haY

/-- Every occurrence is mixed, so the cycle has order exactly two. -/
theorem FourWagonFrame.twiceOrder_eq_four
    (F : D.FourWagonFrame) :
    F.toBigCycle.twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, connectorKind,
    FourWagonFrame.toBigCycle, Fin.sum_univ_four,
    cyclicSucc, twiceOccurrenceWeight]

/-- Reversing the endpoint order also reverses the ambient-pair
edge predicate; this lets A2 use one no-edge hypothesis in both
wagon-connector orientations. -/
private theorem pairEdge_reverse_of_pairEdge
    (x y : V) (h : D.PairEdge y x) : D.PairEdge x y := by
  rcases h with ⟨e, hye, hxe⟩
  exact ⟨e, hxe, hye⟩

/-- A2 is automatic for the alternating location pattern except
for the extra ambient-edge prohibition. The latter is exactly the
single hypothesis that no physical edge joins x and y. -/
theorem FourWagonFrame.A2_of_no_edge
    (F : D.FourWagonFrame)
    (hNoEdge : ¬ D.PairEdge F.x F.y) :
    F.toBigCycle.A2 := by
  have hNoReverse : ¬ D.PairEdge F.y F.x := by
    intro h
    exact hNoEdge (D.pairEdge_reverse_of_pairEdge F.x F.y h)
  constructor
  · intro k w hw j hj
    fin_cases k <;> fin_cases j <;>
      simp_all [BigCycle.InWagonAt,
        FourWagonFrame.toBigCycle, trainCyclicPred, cyclicSucc]
  · intro k w x y hw hleft hright _ _ _
    fin_cases k <;>
      simp_all [FourWagonFrame.toBigCycle,
        trainCyclicPred, cyclicSucc]

/-- For any wagon other than X, old wagon linearity forbids
containing both distinct vertices x,y of X. Hence its positions
lie in one of the two consecutive pairs {0,1} or {2,3}, proving A3. -/
theorem FourWagonFrame.A3_of_linear
    (F : D.FourWagonFrame)
    (hLinear : D.LinearPretrain) :
    F.toBigCycle.A3 := by
  intro w hw
  have hwq : w ≠ F.q := by
    intro h
    apply hw (2 : Fin 4)
    simp [FourWagonFrame.toBigCycle, h]
  have hqX : D.WagonVertex F.q F.x := ⟨F.e, F.heQ, F.heX⟩
  have hqY : D.WagonVertex F.q F.y := ⟨F.f, F.hfQ, F.hfY⟩
  have hNotBoth :
      ¬ (D.WagonVertex w F.x ∧ D.WagonVertex w F.y) := by
    rintro ⟨hx, hy⟩
    have hSmall := hLinear.2 w F.q hwq
    exact F.hxy (hSmall ⟨hx, hqX⟩ ⟨hy, hqY⟩)
  by_cases hx : D.WagonVertex w F.x
  · have hy : ¬ D.WagonVertex w F.y := by
      intro hy
      exact hNotBoth ⟨hx, hy⟩
    refine ⟨(0 : Fin 4), ?_⟩
    intro j hj
    fin_cases j <;>
      simp_all [BigCycle.InWagonAt,
        FourWagonFrame.toBigCycle, cyclicSucc]
  · refine ⟨(2 : Fin 4), ?_⟩
    intro j hj
    fin_cases j <;>
      simp_all [BigCycle.InWagonAt,
        FourWagonFrame.toBigCycle, cyclicSucc]

/-- The four-occurrence cycle satisfies literal A1--A3 under
only old wagon linearity and the ambient x,y non-edge guard. -/
theorem FourWagonFrame.acceptable
    (F : D.FourWagonFrame)
    (hLinear : D.LinearPretrain)
    (hNoEdge : ¬ D.PairEdge F.x F.y) :
    F.toBigCycle.Acceptable := by
  refine ⟨?_, F.A2_of_no_edge hNoEdge, F.A3_of_linear hLinear⟩
  intro hOrder
  have hFour : F.toBigCycle.twiceOrder = 4 :=
    F.twiceOrder_eq_four
  omega

/-- In the old standard picture, a supreme designated copy containing
two distinct boundary core vertices is forced by its boundary
intersection property to contribute an actual edge through the pair.
This theorem isolates the FINITE-CYCLE contradiction; the geometric
boundary-intersection hypothesis is passed explicitly.

It is the missing intrinsic step of the unrestricted two-standard
lemma, with no invalid deduction from mere vertex/wagon incidence. -/
theorem FourWagonFrame.pairEdge_of_system_bound_and_boundary
    (F : D.FourWagonFrame)
    (hFull : D.FullSystemGirthGT 2)
    (hCompatible : D.CopyEdgeCarrierCompatible)
    (hBoundary : ∀ i : I,
      F.x ∈ D.copyCarrier i →
      F.y ∈ D.copyCarrier i →
      D.PairEdge F.x F.y) :
    D.PairEdge F.x F.y := by
  by_contra hNoEdge
  have hAccept : F.toBigCycle.Acceptable :=
    F.acceptable hFull.1 hNoEdge
  have hOrder : F.toBigCycle.twiceOrder ≤ 2 * 2 := by
    rw [F.twiceOrder_eq_four]
  have hSup : F.toBigCycle.HasSimultaneousSupreme :=
    hFull.2 4 F.toBigCycle hAccept hOrder
  obtain ⟨k, i, _hki, hAll⟩ :=
    BigCycle.supreme_copy_contains_vertex_connectors D
      F.toBigCycle hCompatible hSup
  have hx : F.x ∈ D.copyCarrier i :=
    hAll (1 : Fin 4) F.x (by rfl)
  have hy : F.y ∈ D.copyCarrier i :=
    hAll (3 : Fin 4) F.y (by rfl)
  exact hNoEdge (hBoundary i hx hy)

end StructuralRamsey.Girth.OrderOneData

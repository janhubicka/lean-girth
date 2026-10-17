import Girth.TrainArbitraryLongA2Geometry
import Girth.TrainArbitraryLongOrder
import Girth.TrainA2ContactTransfer

/-!
# Circulation: output A2 needs only physical long-boundary geometry

The existing conditional A2 theorem encodes a fresh output wagon by
LongValid, which additionally insists that both new edges come from
one designated source label. That membership is not needed by A2.

Here a fresh wagon is instead certified by its two ORIGINAL boundary
vertices in that wagon, their nonedge condition, and the exact
predecessor/successor index equations. The source A3 window makes
those the only old vertex contacts of the fresh wagon.

This is the label-independent A2 transfer interface required for
arbitrary admissible replacement. Output A2 is the CONCLUSION, and
no output acceptability, wagon linearity, PlanValid, supreme label,
or appendix theorem is assumed.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Each output wagon connector is either inherited at the exact
old neighbour positions, or fresh at the two old vertex boundaries
of a nonedge pair in one wagon. No designated-label provenance. -/
def BigCycle.OutputWagonGeometricCase
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (oldPos : Fin n → Fin m) (j : Fin m) (p : P) : Prop :=
  (∃ i : Fin n,
    j = oldPos i ∧
    C.connector i = Sum.inr p ∧
    oldPos (trainCyclicPred i) = trainCyclicPred j ∧
    oldPos (cyclicSucc i) = cyclicSucc j)
  ∨
  (∃ (i : Fin n) (x y : V),
    C.connector (trainCyclicPred i) = Sum.inl x ∧
    C.connector i = Sum.inl y ∧
    D.WagonVertex p x ∧ D.WagonVertex p y ∧
    (∀ t : Fin n, C.connector t ≠ Sum.inr p) ∧
    ¬ D.PairEdge x y ∧
    oldPos (trainCyclicPred i) = trainCyclicPred j ∧
    oldPos i = cyclicSucc j)

/-- Transfer BOTH clauses of A2 from source to output using only
the correct physical connector-position cases. A3 is used solely to
confine the old contacts of a fresh wagon to its two boundaries. -/
theorem BigCycle.A2_of_geometric_output_wagon_cases
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hA2 : C.A2) (hA3 : C.A3)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (hContactPullback : ∀ (p : P) (j : Fin m),
      B.InWagonAt p j →
      ∃ i : Fin n, j = oldPos i ∧ C.InWagonAt p i)
    (hCases : ∀ (j : Fin m) (p : P),
      B.connector j = Sum.inr p →
      C.OutputWagonGeometricCase D B oldPos j p) :
    B.A2 := by
  constructor
  · intro j p hj t ht
    obtain ⟨u, htu, hu⟩ := hContactPullback p t ht
    rcases hCases j p hj with hOld | hNew
    · obtain ⟨i, hji, hi, hPrevPos, hSuccPos⟩ := hOld
      rcases hA2.1 i p hi u hu with hBefore | hAfter
      · left
        calc
          t = oldPos u := htu
          _ = oldPos (trainCyclicPred i) := congrArg oldPos hBefore
          _ = trainCyclicPred j := hPrevPos
      · right
        calc
          t = oldPos u := htu
          _ = oldPos (cyclicSucc i) := congrArg oldPos hAfter
          _ = cyclicSucc j := hSuccPos
    · obtain ⟨i, x, y, hCx, hCy, hPx, hPy, hFresh,
        _hNoPair, hPrevPos, hHerePos⟩ := hNew
      have hDistinct : trainCyclicPred i ≠ i := by
        intro hEq
        have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i
        rw [hEq] at hs
        exact (C.ne_cyclicSucc D i) hs.symm
      have hBefore : C.InWagonAt p (trainCyclicPred i) :=
        ⟨x, hCx, hPx⟩
      have hAfter : C.InWagonAt p i :=
        ⟨y, hCy, hPy⟩
      have hWindow :=
        C.nonconnector_two_contact_window D hA3 p hFresh
          (trainCyclicPred i) i hDistinct hBefore hAfter u hu
      rcases hWindow with hBefore | hAfter
      · left
        calc
          t = oldPos u := htu
          _ = oldPos (trainCyclicPred i) := congrArg oldPos hBefore
          _ = trainCyclicPred j := hPrevPos
      · right
        calc
          t = oldPos u := htu
          _ = oldPos i := congrArg oldPos hAfter
          _ = cyclicSucc j := hHerePos
  · intro j p x y hj hPrev hSucc hDifferent hPx hPy
    rcases hCases j p hj with hOld | hNew
    · obtain ⟨i, hji, hi, hPredPos, hSuccPos⟩ := hOld
      have hOldPrev : C.connector (trainCyclicPred i) = Sum.inl x := by
        calc
          C.connector (trainCyclicPred i) =
              B.connector (oldPos (trainCyclicPred i)) :=
                (hConnector _).symm
          _ = B.connector (trainCyclicPred j) :=
              congrArg B.connector hPredPos
          _ = Sum.inl x := hPrev
      have hOldSucc : C.connector (cyclicSucc i) = Sum.inl y := by
        calc
          C.connector (cyclicSucc i) =
              B.connector (oldPos (cyclicSucc i)) :=
                (hConnector _).symm
          _ = B.connector (cyclicSucc j) :=
              congrArg B.connector hSuccPos
          _ = Sum.inl y := hSucc
      have hOldDifferent :
          trainCyclicPred i ≠ cyclicSucc i := by
        intro heq
        apply hDifferent
        calc
          trainCyclicPred j = oldPos (trainCyclicPred i) := hPredPos.symm
          _ = oldPos (cyclicSucc i) := congrArg oldPos heq
          _ = cyclicSucc j := hSuccPos
      exact hA2.2 i p x y hi hOldPrev hOldSucc
        hOldDifferent hPx hPy
    · obtain ⟨i, a, b, hCa, hCb, _hWa, _hWb, _hFresh,
        hNonedge, hPredPos, hHerePos⟩ := hNew
      have hOutputPrev : B.connector (trainCyclicPred j) = Sum.inl a := by
        calc
          B.connector (trainCyclicPred j) =
              B.connector (oldPos (trainCyclicPred i)) :=
                congrArg B.connector hPredPos.symm
          _ = C.connector (trainCyclicPred i) := hConnector _
          _ = Sum.inl a := hCa
      have hOutputNext : B.connector (cyclicSucc j) = Sum.inl b := by
        calc
          B.connector (cyclicSucc j) =
              B.connector (oldPos i) :=
                congrArg B.connector hHerePos.symm
          _ = C.connector i := hConnector i
          _ = Sum.inl b := hCb
      have hxx : x = a :=
        Sum.inl.inj (hPrev.symm.trans hOutputPrev)
      have hyy : y = b :=
        Sum.inl.inj (hSucc.symm.trans hOutputNext)
      rw [hxx, hyy]
      exact hNonedge

/-- All output vertex connectors are inherited, so a separate opaque
contact-pullback hypothesis can be replaced by the oldPos vertex
provenance already checked for literal replacement words. -/
theorem BigCycle.A2_of_preserved_vertices_and_geometric_wagons
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hA2 : C.A2) (hA3 : C.A3)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (hVertexPos : ∀ (j : Fin m) (x : V),
      B.connector j = Sum.inl x →
      ∃ i : Fin n, j = oldPos i)
    (hCases : ∀ (j : Fin m) (p : P),
      B.connector j = Sum.inr p →
      C.OutputWagonGeometricCase D B oldPos j p) :
    B.A2 := by
  apply C.A2_of_geometric_output_wagon_cases
    D B hA2 hA3 oldPos hConnector
  · exact C.wagon_contacts_pullback_of_vertex_positions
      D B oldPos hConnector hVertexPos
  · exact hCases

end StructuralRamsey.Girth.OrderOneData

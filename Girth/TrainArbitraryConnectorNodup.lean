import Girth.TrainArbitraryLongA2Geometry
import Girth.TrainInsertedConnectorNodup
import Girth.TrainFreshLongWagon

/-!
# Circulation: connector injectivity for arbitrary geometric replacements

Under source (A3), a fresh wagon with two distinct old vertex contacts
determines its insertion source occurrence uniquely, once the source
length is at least three. Thus different locally valid long pieces
cannot insert the same wagon even if their physical edges are not
taken from a single selected designated copy.

This generalizes the earlier strict PlanValid connector-nodup proof:
all original connectors survive; every new wagon is fresh from them;
and the two-contact window forbids duplicate new wagons. Hence the
actual flattened arbitrary-replacement connector list is duplicate-free.

This is one of the five intrinsic CyclicWordChecks for automatic
legality of arbitrary replacements. It uses no selected label,
PlanValid, constructed output BigCycle, or appendix theorem.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Distinct long insertion positions cannot have the same fresh
wagon if their original boundary vertices lie in that wagon. -/
theorem BigCycle.arbitrary_long_wagons_pairwise
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongBoundaryGeometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (i j : Fin n) (hij : i ≠ j)
    (e f g h : E) (p q : P)
    (hi : pieces i = .long e p f)
    (hj : pieces j = .long g q h) :
    p ≠ q := by
  intro heq
  subst q
  obtain ⟨x, y, hPrevI, hHereI, hPx, hPy⟩ :=
    hGeom i e f p hi
  obtain ⟨u, v, hPrevJ, hHereJ, hPu, hPv⟩ :=
    hGeom j g h p hj
  have hIPrev : C.InWagonAt p (trainCyclicPred i) :=
    ⟨x, hPrevI, hPx⟩
  have hIHere : C.InWagonAt p i :=
    ⟨y, hHereI, hPy⟩
  have hJPrev : C.InWagonAt p (trainCyclicPred j) :=
    ⟨u, hPrevJ, hPu⟩
  have hJHere : C.InWagonAt p j :=
    ⟨v, hHereJ, hPv⟩
  exact hij (C.nonconnector_wagon_boundary_occurrence_unique
    D hAccept hn p (hFresh i e p f hi)
    i j hIPrev hIHere hJPrev hJHere)

/-- The actual ordered connector list of any arbitrary fresh
locally geometric replacement is duplicate-free at length >=3. -/
theorem BigCycle.arbitrary_resultWord_connectors_nodup
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongBoundaryGeometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    ((C.resultWord D pieces).map Prod.snd).Nodup := by
  rw [C.resultWord_connectorList D pieces]
  apply optionalConnectorWord_nodup
    C.connector (C.insertedConnector D pieces)
  · exact C.connector_injective
  · intro i j a ha
    cases hp : pieces i with
    | keep =>
        simp [BigCycle.insertedConnector, hp] at ha
    | short e =>
        simp [BigCycle.insertedConnector, hp] at ha
    | long e p f =>
        have heq : a = (Sum.inr p : V ⊕ P) := by
          simpa [BigCycle.insertedConnector, hp] using ha.symm
        subst a
        exact (hFresh i e p f hp j).symm
  · intro i j a b hij ha hb
    cases hp : pieces i with
    | keep =>
        simp [BigCycle.insertedConnector, hp] at ha
    | short e =>
        simp [BigCycle.insertedConnector, hp] at ha
    | long e p f =>
        have heqA : a = (Sum.inr p : V ⊕ P) := by
          simpa [BigCycle.insertedConnector, hp] using ha.symm
        cases hq : pieces j with
        | keep =>
            simp [BigCycle.insertedConnector, hq] at hb
        | short g =>
            simp [BigCycle.insertedConnector, hq] at hb
        | long g q h =>
            have heqB : b = (Sum.inr q : V ⊕ P) := by
              simpa [BigCycle.insertedConnector, hq] using hb.symm
            have hDifferent : p ≠ q :=
              C.arbitrary_long_wagons_pairwise D hAccept hn
                pieces hGeom hFresh i j hij e f g h p q hp hq
            intro hab
            apply hDifferent
            exact Sum.inr.inj (heqA.symm.trans (hab.trans heqB))

end StructuralRamsey.Girth.OrderOneData

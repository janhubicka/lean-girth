import Girth.TrainArbitraryLongA3
import Girth.TrainA2ContactTransfer

/-!
# Circulation: A2 geometry without one common supreme source label

The short/long words of an arbitrary replacement do not necessarily
draw their new edges from one selected designated source copy.
Nevertheless (A2) of an actual expanded output uses only:
* each long insertion's two original vertex boundaries in its wagon;
* the source wagon-contact window (A3);
* the physical nonedge condition between these two vertices.

We separate exactly those properties from the stricter LongValid
predicate, whose edge-membership clauses are irrelevant for A2/A3.
This supplies a reusable abstract source-side interface for the
full arbitrary-replacement lemma, with no appendix theorem.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A wagon absent from the source connector word whose carrier meets
two DISTINCT source connector positions can meet no other positions.
This is precisely the two-position content of A3, independently of
how those two contacts were constructed. -/
theorem BigCycle.nonconnector_two_contact_window
    {n : ℕ} (C : D.BigCycle n) (hA3 : C.A3)
    (p : P) (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (i j : Fin n) (hij : i ≠ j)
    (hi : C.InWagonAt p i) (hj : C.InWagonAt p j) :
    ∀ t : Fin n, C.InWagonAt p t → t = i ∨ t = j := by
  obtain ⟨root, hWindow⟩ := hA3 p hFresh
  have hI := hWindow i hi
  have hJ := hWindow j hj
  intro t ht
  have hT := hWindow t ht
  rcases hI with hI | hI
  · rcases hJ with hJ | hJ
    · exact False.elim (hij (hI.trans hJ.symm))
    · rcases hT with hT | hT
      · exact Or.inl (hT.trans hI.symm)
      · exact Or.inr (hT.trans hJ.symm)
  · rcases hJ with hJ | hJ
    · rcases hT with hT | hT
      · exact Or.inr (hT.trans hJ.symm)
      · exact Or.inl (hT.trans hI.symm)
    · exact False.elim (hij (hI.trans hJ.symm))

/-- The geometric conditions on a long piece necessary to transfer
BOTH A2 clauses, without requiring either replacement edge to belong
to one fixed supreme label (or even any old occurrence label). -/
def BigCycle.LocalLongA2Geometry
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) : Prop :=
  ∀ (i : Fin n) (e f : E) (p : P),
    pieces i = .long e p f →
    ∃ x y : V,
      C.connector (trainCyclicPred i) = Sum.inl x ∧
      C.connector i = Sum.inl y ∧
      D.WagonVertex p x ∧ D.WagonVertex p y ∧
      ¬ D.PairEdge x y

/-- The A2 input contains all the geometry needed by the already
checked arbitrary A3 transfer; there is no second family of
additional geometry assumptions. -/
theorem BigCycle.localLongBoundaryGeometry_of_A2
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry D pieces) :
    C.LocalLongBoundaryGeometry D pieces := by
  intro i e f p hp
  obtain ⟨x, y, hPrev, hHere, hPx, hPy, _hNoPair⟩ :=
    hGeom i e f p hp
  exact ⟨x, y, hPrev, hHere, hPx, hPy⟩

/-- Two old source boundary contacts of any physically valid fresh
long insertion exhaust all old vertex contacts of that wagon, even
if the replacement edges come from unrelated source labels. -/
theorem BigCycle.fresh_wagon_contacts_of_localA2Geometry
    {n : ℕ} (C : D.BigCycle n) (hA3 : C.A3)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (i : Fin n) (e f : E) (p : P)
    (hi : pieces i = .long e p f)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    ∀ t : Fin n, C.InWagonAt p t →
      t = trainCyclicPred i ∨ t = i := by
  obtain ⟨x, y, hPrev, hHere, hPx, hPy, _hNoPair⟩ :=
    hGeom i e f p hi
  have hBefore : C.InWagonAt p (trainCyclicPred i) :=
    ⟨x, hPrev, hPx⟩
  have hAfter : C.InWagonAt p i :=
    ⟨y, hHere, hPy⟩
  have hDistinct : trainCyclicPred i ≠ i := by
    intro heq
    have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i
    rw [heq] at hs
    exact (C.ne_cyclicSucc D i) hs.symm
  exact C.nonconnector_two_contact_window D hA3 p hFresh
    (trainCyclicPred i) i hDistinct hBefore hAfter

/-- Immediate A3 consequence of the same weaker physical A2 geometry,
without any PlanValid or fixed selected source label assumption. -/
theorem BigCycle.output_A3_of_arbitrary_A2Geometry
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hA3 : C.A3) (hLinear : D.LinearPretrain)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces) :
    B.A3 :=
  C.output_A3_of_arbitrary_long_geometry D B hA3 hLinear pieces
    (C.localLongBoundaryGeometry_of_A2 D pieces hGeom)
    hFresh hWord

end StructuralRamsey.Girth.OrderOneData

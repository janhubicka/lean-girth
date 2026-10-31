import Girth.TrainFillingContractionPositions
import Girth.TrainCyclicRestriction

/-!
# The edge-sensitive restriction premise for filling

Old pair edges do not generally lift to filled pair edges. The relevant
claim is instead vacuous: an old joining edge at a surviving wagon would
make that source position contractible. A legal projected cycle remains
an explicit input here; TrainFillingProjectedCycle constructs it separately.
-/
namespace StructuralRamsey.Girth.TrainFilling
universe v
variable {V I P : Type v}
variable (F : TrainFilling V) (copyCarrier : I → Set V)
variable (copyEdges : I → Set F.OldEdge) (parent : F.OldEdge → P)
local notation "O" => F.oldData copyCarrier copyEdges parent
local notation "H" => F.filledData copyCarrier copyEdges parent

theorem retained_wagon_no_old_pair
    {n m : ℕ} (C : (H).BigCycle n) (B : (O).BigCycle m)
    (hA2 : C.A2) (position : Fin m ↪o Fin n)
    (hConnector : ∀ j, C.connector (position j) = B.connector j)
    (hRetained : ∀ j, ¬ F.ContractibleBlock copyCarrier copyEdges parent C (position j))
    (j : Fin m) (p : P) (x y : V)
    (hj : B.connector j = Sum.inr p)
    (hx : B.connector (trainCyclicPred j) = Sum.inl x)
    (hy : B.connector (cyclicSucc j) = Sum.inl y)
    (hDifferent : trainCyclicPred j ≠ cyclicSucc j)
    (hpx : (O).WagonVertex p x) (hpy : (O).WagonVertex p y) :
    ¬ (O).PairEdge x y := by
  intro hPair
  have hpSource : C.connector (position j) = Sum.inr p := (hConnector j).trans hj
  have hxSource : C.connector (position (trainCyclicPred j)) = Sum.inl x :=
    (hConnector _).trans hx
  have hySource : C.connector (position (cyclicSucc j)) = Sum.inl y :=
    (hConnector _).trans hy
  have hxFilled := (F.wagonVertex_filled_iff_old copyCarrier copyEdges parent p x).mpr hpx
  have hyFilled := (F.wagonVertex_filled_iff_old copyCarrier copyEdges parent p y).mpr hpy
  have hPred : position (trainCyclicPred j) = trainCyclicPred (position j) := by
    rcases hA2.1 (position j) p hpSource
        (position (trainCyclicPred j)) ⟨x, hxSource, hxFilled⟩ with h | h
    · exact h
    · exact False.elim (hDifferent
        (CyclicRestriction.successor_of_source_successor position
          j (trainCyclicPred j) h))
  have hSucc : position (cyclicSucc j) = cyclicSucc (position j) := by
    rcases hA2.1 (position j) p hpSource
        (position (cyclicSucc j)) ⟨y, hySource, hyFilled⟩ with h | h
    · have hbad := CyclicRestriction.predecessor_of_source_predecessor
        B.length_ge_two C.length_ge_two position j (cyclicSucc j) h
      exact False.elim (hDifferent hbad.symm)
    · exact h
  have hSourceDifferent : trainCyclicPred (position j) ≠ cyclicSucc (position j) := by
    intro h
    apply hDifferent
    apply position.injective
    exact hPred.trans (h.trans hSucc.symm)
  apply hRetained j
  refine ⟨p, x, y, hpSource, ?_, ?_, hSourceDifferent, hxFilled, hyFilled, hPair⟩
  · rw [← hPred]
    exact hxSource
  · rw [← hSucc]
    exact hySource

def fillingRestrictionMap
    {n m : ℕ} (C : (H).BigCycle n) (B : (O).BigCycle m)
    (hA2 : C.A2) (position : Fin m ↪o Fin n)
    (hConnector : ∀ j, C.connector (position j) = B.connector j)
    (hRetained : ∀ j, ¬ F.ContractibleBlock copyCarrier copyEdges parent C (position j)) :
    C.RestrictionMap B where
  position := position
  vertex := id
  wagon := id
  vertex_injective := fun _ _ h => h
  wagon_injective := fun _ _ h => h
  connector_eq := by
    intro j
    rw [hConnector j]
    cases B.connector j <;> rfl
  contact := by
    intro p _j x _hx hpx
    exact (F.wagonVertex_filled_iff_old copyCarrier copyEdges parent p x).mpr hpx
  pair_reflect := by
    intro j p x y hj hx hy hDifferent hpx hpy hPair
    exact False.elim (F.retained_wagon_no_old_pair copyCarrier copyEdges parent
      C B hA2 position hConnector hRetained j p x y hj hx hy hDifferent hpx hpy hPair)

theorem filling_restriction_bounds
    {n m : ℕ} (C : (H).BigCycle n) (B : (O).BigCycle m)
    (hAccept : C.Acceptable) (position : Fin m ↪o Fin n)
    (hConnector : ∀ j, C.connector (position j) = B.connector j)
    (hRetained : ∀ j, ¬ F.ContractibleBlock copyCarrier copyEdges parent C (position j)) :
    m ≤ n ∧ B.twiceOrder ≤ C.twiceOrder ∧ B.A2 ∧ B.A3 := by
  let R := F.fillingRestrictionMap copyCarrier copyEdges parent
    C B hAccept.2.1 position hConnector hRetained
  exact R.restrict hAccept.2.1 hAccept.2.2

theorem filling_canonical_restriction_bounds
    {n : ℕ} (C : (H).BigCycle n)
    (B : (O).BigCycle (F.retainedPositions copyCarrier copyEdges parent C).card)
    (hAccept : C.Acceptable)
    (hConnector : ∀ j,
      C.connector (F.retainedIndex copyCarrier copyEdges parent C j) = B.connector j) :
    (F.retainedPositions copyCarrier copyEdges parent C).card ≤ n ∧
      B.twiceOrder ≤ C.twiceOrder ∧ B.A2 ∧ B.A3 := by
  exact F.filling_restriction_bounds copyCarrier copyEdges parent C B hAccept
    (F.retainedIndex copyCarrier copyEdges parent C) hConnector
    (F.retainedIndex_not_contractible copyCarrier copyEdges parent C)
end StructuralRamsey.Girth.TrainFilling

import Girth.TrainOutputA3SplitReduction
import Girth.TrainOptionalOldCyclic
import Mathlib.Tactic

/-!
# Circulation: transport cyclic old successors to the actual output word

The generic optional-insertion successor theorem is applied to the literal
connector projection of resultWord.  The only indexing conversion is the
length-preserving cast from the actual output BigCycle's Fin m indices to
the expanded connector list; uniqueness of connectors identifies the oldPos
successor.  The checked A3 split reduction can then be instantiated.

This proves output A3 for a legal literal PlanValid replacement, conditional
only on the usual source acceptability/linearity, literal output BigCycle,
and stated freshness.  It does not prove output A2 or the existence of the
output BigCycle and makes no claim about the later girth-preservation step.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The old source connector at i is followed in the actual expanded
BigCycle by the old connector at cyclicSucc i whenever the next source
block has no inserted fresh wagon.  In particular the wrap is included. -/
theorem BigCycle.literal_oldPos_successor_of_noInsertion
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hFresh : ∀ (r : Fin n) (e : E) (p : P) (f : E),
      pieces r = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (i : Fin n)
    (hNone : C.insertedConnector D pieces (cyclicSucc i) = none) :
    oldPos (cyclicSucc i) = cyclicSucc (oldPos i) := by
  cases n with
  | zero =>
      have hn := C.length_ge_two
      omega
  | succ n' =>
      have hInsertFresh :
          ∀ (r t : Fin (n' + 1)) (a : V ⊕ P),
            C.insertedConnector D pieces r = some a →
            a ≠ C.connector t := by
        intro r t a ha
        cases hp : pieces r with
        | keep =>
            simp [BigCycle.insertedConnector, hp] at ha
        | short e =>
            simp [BigCycle.insertedConnector, hp] at ha
        | long e p f =>
            have hap : a = (Sum.inr p : V ⊕ P) := by
              simpa [BigCycle.insertedConnector, hp] using ha.symm
            subst a
            exact (hFresh r e p f hp t).symm
      let w : List (V ⊕ P) :=
        optionalConnectorWord C.connector (C.insertedConnector D pieces)
      have hConnectors : List.ofFn B.connector = w := by
        calc
          List.ofFn B.connector =
              (List.ofFn (fun j : Fin m =>
                (B.label j, B.connector j))).map Prod.snd := by
                  simp [List.map_ofFn, Function.comp_def]
          _ = (C.resultWord D pieces).map Prod.snd :=
                congrArg (List.map Prod.snd) hWord
          _ = w := C.resultWord_connectorList D pieces
      have hLen : m = w.length := by
        have hh := congrArg List.length hConnectors
        simpa using hh
      have hAt (j : Fin m) :
          w.get (Fin.cast hLen j) = B.connector j := by
        have hPoint := congrArg
          (fun xs : List (V ⊕ P) => xs[j.val]?) hConnectors
        have hjLt : j.val < (List.ofFn B.connector).length := by
          simpa using j.isLt
        have hLeft :
            (List.ofFn B.connector)[j.val]? =
              some (B.connector j) := by
          simpa [List.get_ofFn] using
            (List.getElem?_eq_getElem hjLt)
        have hRight :
            w[j.val]? = some (w.get (Fin.cast hLen j)) :=
          List.getElem?_eq_getElem (Fin.cast hLen j).isLt
        exact Option.some.inj (hRight.symm.trans (hPoint.symm.trans hLeft))
      have hCastSucc (j : Fin m) :
          Fin.cast hLen (cyclicSucc j) =
            cyclicSucc (Fin.cast hLen j) := by
        apply Fin.ext
        change (j.val + 1) % m = (j.val + 1) % w.length
        exact congrArg (fun z : ℕ => (j.val + 1) % z) hLen
      have hj : w.get (Fin.cast hLen (oldPos i)) = C.connector i :=
        (hAt (oldPos i)).trans (hConnector i)
      have hSucc :
          w.get (cyclicSucc (Fin.cast hLen (oldPos i))) =
            C.connector (cyclicSucc i) := by
        exact optionalConnectorWord_old_cyclic_successor
          C.connector (C.insertedConnector D pieces)
          C.connector_injective hInsertFresh
          i hNone (Fin.cast hLen (oldPos i)) hj
      have hActual :
          B.connector (cyclicSucc (oldPos i)) =
            C.connector (cyclicSucc i) := by
        calc
          B.connector (cyclicSucc (oldPos i)) =
              w.get (Fin.cast hLen (cyclicSucc (oldPos i))) :=
                (hAt _).symm
          _ = w.get (cyclicSucc (Fin.cast hLen (oldPos i))) := by
                rw [hCastSucc]
          _ = C.connector (cyclicSucc i) := hSucc
      apply B.connector_injective
      exact (hConnector (cyclicSucc i)).trans hActual.symm

/-- Output A3 for the ACTUAL literal replacement BigCycle, with no
opaque oldPos/no-split hypothesis.  All geometric hypotheses are the
existing source PlanValid, source acceptability and linear pretrain. -/
theorem BigCycle.output_A3_of_literal_resultWord
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (r : Fin n) (e : E) (p : P) (f : E),
      pieces r = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces) :
    B.A3 := by
  obtain ⟨oldPos, hConnector, hVertexPos⟩ :=
    C.oldPos_exists_of_literal_resultWord D B pieces hWord
  apply C.output_A3_of_noInsertionSuccessor
    D B hAccept hLinear k pieces hPlan hWord
      oldPos hConnector hVertexPos
  intro i hNone
  exact C.literal_oldPos_successor_of_noInsertion
    D B pieces hFresh hWord oldPos hConnector i hNone

end StructuralRamsey.Girth.OrderOneData

import Girth.TrainLiteralOldPosA3
import Girth.TrainOptionalOldHeadCyclic

/-!
# Circulation: the old-to-next-block rule in the actual output BigCycle

Apply the generic cyclic old-connector successor lemma to the actual
physical connector projection of the literal replacement word. The
proof uses only a length-preserving Fin index cast and connector
injectivity, not output A2/A3 or wagon linearity.

The successor of an old connector is exactly the first token of the
next source block. The inserted case is the remaining old-to-fresh
position equality used in A2; the no-insertion case is the previously
checked A3 oldPos successor equation.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Physical output old-connector successor, whether the next piece
inserts a fresh wagon or not. -/
theorem BigCycle.literal_oldPos_cyclic_head
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
    (i : Fin n) :
    B.connector (cyclicSucc (oldPos i)) =
      optionalConnectorHead C.connector (C.insertedConnector D pieces)
        (cyclicSucc i) := by
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
            optionalConnectorHead C.connector
              (C.insertedConnector D pieces) (cyclicSucc i) := by
        exact optionalConnectorWord_old_cyclic_head
          C.connector (C.insertedConnector D pieces)
          C.connector_injective hInsertFresh
          i (Fin.cast hLen (oldPos i)) hj
      calc
        B.connector (cyclicSucc (oldPos i)) =
            w.get (Fin.cast hLen (cyclicSucc (oldPos i))) :=
              (hAt _).symm
        _ = w.get (cyclicSucc (Fin.cast hLen (oldPos i))) := by
              rw [hCastSucc]
        _ = optionalConnectorHead C.connector
              (C.insertedConnector D pieces) (cyclicSucc i) := hSucc

/-- If the next block inserts a wagon a, its physical output position
is exactly the cyclic successor of the preceding old connector. -/
theorem BigCycle.literal_oldPos_successor_inserted
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
    (i : Fin n) (a : V ⊕ P)
    (hSome : C.insertedConnector D pieces (cyclicSucc i) = some a) :
    B.connector (cyclicSucc (oldPos i)) = a := by
  simpa [optionalConnectorHead, hSome] using
    (C.literal_oldPos_cyclic_head
      D B pieces hFresh hWord oldPos hConnector i)

end StructuralRamsey.Girth.OrderOneData

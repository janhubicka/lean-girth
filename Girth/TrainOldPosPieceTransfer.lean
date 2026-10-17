import Girth.TrainLiteralOldPosA3
import Girth.TrainLongBoundaryCollision

/-!
# Circulation: transport later pieces across an unchanged old boundary

For the global composition of a first replacement with a later
supreme plan, the easy source blocks are the keep and short blocks.
They insert no wagon, so the output predecessor of oldPos(i) is
exactly oldPos(pred(i)). This follows from the checked cyclic
optional-word successor lemma, including the last-to-first boundary.

Consequently a later ShortValid or LongValid piece at oldPos(i)
is a valid source piece at i, provided the later chosen designated
label is the same physical label as the chosen source target.

This does not use strict PlanValid for the FIRST replacement,
source acceptability, output A2/A3, or an appendix theorem.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- For a block with no fresh insertion, its inherited right
connector has the inherited preceding old connector as predecessor
in the actual output BigCycle, even at the cyclic wrap. -/
theorem BigCycle.literal_oldPos_pred_of_noInsertion
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hFresh : ∀ (r : Fin n) (e : E) (p : P) (f : E),
      pieces r = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (i : Fin n)
    (hNone : C.insertedConnector D pieces i = none) :
    trainCyclicPred (oldPos i) = oldPos (trainCyclicPred i) := by
  have hNonePrev :
      C.insertedConnector D pieces
        (cyclicSucc (trainCyclicPred i)) = none := by
    simpa [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i]
      using hNone
  have hSucc :
      oldPos i = cyclicSucc (oldPos (trainCyclicPred i)) := by
    simpa [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i]
      using (C.literal_oldPos_successor_of_noInsertion
        D B pieces hFresh hWord oldPos hConnector
          (trainCyclicPred i) hNonePrev)
  have hPred := congrArg trainCyclicPred hSucc
  simpa [trainCyclicPred_cyclicSucc_of_two_le
    B.length_ge_two (oldPos (trainCyclicPred i))] using hPred

/-- A later short piece at the unchanged output old position gives a
genuine source short piece with the original two boundaries. -/
theorem BigCycle.shortValid_transport_oldPos_noInsertion
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hFresh : ∀ (r : Fin n) (e : E) (p : P) (f : E),
      pieces r = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (kC : Fin n) (kB : Fin m)
    (hTarget : B.label kB = C.label kC)
    (i : Fin n)
    (hNone : C.insertedConnector D pieces i = none)
    (e : E)
    (hLater : B.ShortValid D kB (oldPos i) e) :
    C.ShortValid D kC i e := by
  have hPred := C.literal_oldPos_pred_of_noInsertion
    D B pieces hFresh hWord oldPos hConnector i hNone
  rcases hLater with ⟨he, hBefore, hHere⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hTarget] using he
  · simpa only [hPred, hConnector] using hBefore
  · simpa only [hConnector] using hHere

/-- Analogous transport of a later genuine long piece. The new
wagon's nonedge condition and physical witnesses are unchanged. -/
theorem BigCycle.longValid_transport_oldPos_noInsertion
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hFresh : ∀ (r : Fin n) (e : E) (p : P) (f : E),
      pieces r = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (kC : Fin n) (kB : Fin m)
    (hTarget : B.label kB = C.label kC)
    (i : Fin n)
    (hNone : C.insertedConnector D pieces i = none)
    (e f : E) (p : P)
    (hLater : B.LongValid D kB (oldPos i) e p f) :
    C.LongValid D kC i e p f := by
  have hPred := C.literal_oldPos_pred_of_noInsertion
    D B pieces hFresh hWord oldPos hConnector i hNone
  obtain ⟨x, y, hBefore, hHere, he, hf, hDistinct,
    hPe, hPf, hXe, hYf, hNonedge⟩ := hLater
  exact ⟨x, y,
    by simpa only [hPred, hConnector] using hBefore,
    by simpa only [hConnector] using hHere,
    by simpa only [hTarget] using he,
    by simpa only [hTarget] using hf,
    hDistinct, hPe, hPf, hXe, hYf, hNonedge⟩

end StructuralRamsey.Girth.OrderOneData

import Girth.TrainOldPosPieceTransfer

/-!
# Circulation: compose a later piece across a non-inserting first block

When the first replacement contributes no new connector at i,
the checked oldPos predecessor formula makes later ShortValid and
LongValid pieces at oldPos(i) source-valid at i. A later fresh wagon
is also fresh against every source connector, which survives in the
first output. The target label must be the same physical label.

This lemma provides a single source-side short/long alternative
suitable for the local-witness assembly theorem. No appendix input.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

theorem BigCycle.local_witness_of_later_noInsertion
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (first : Fin n → TrainSupremePiece E P)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      first i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D first)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (kC : Fin n) (kB : Fin m)
    (hTarget : B.label kB = C.label kC)
    (later : Fin m → TrainSupremePiece E P)
    (hPlan : B.PlanValid D kB later)
    (hLaterFresh : ∀ (j : Fin m) (e : E) (p : P) (f : E),
      later j = .long e p f →
      ∀ t : Fin m, B.connector t ≠ Sum.inr p)
    (i : Fin n)
    (hNone : C.insertedConnector D first i = none)
    (hNotTarget : B.label (oldPos i) ≠ B.label kB) :
    (∃ e : E, C.ShortValid D kC i e) ∨
      (∃ (e f : E) (p : P),
        C.LongValid D kC i e p f ∧
        ∀ t : Fin n, C.connector t ≠ Sum.inr p) := by
  have hv := (hPlan (oldPos i)).2 hNotTarget
  cases hp : later (oldPos i) with
  | keep =>
      simp [hp] at hv
  | short e =>
      have hShort : B.ShortValid D kB (oldPos i) e := by
        simpa [hp] using hv
      exact Or.inl ⟨e,
        C.shortValid_transport_oldPos_noInsertion
          D B first hFresh hWord oldPos hConnector
          kC kB hTarget i hNone e hShort⟩
  | long e p f =>
      have hLong : B.LongValid D kB (oldPos i) e p f := by
        simpa [hp] using hv
      have hSource : C.LongValid D kC i e p f :=
        C.longValid_transport_oldPos_noInsertion
          D B first hFresh hWord oldPos hConnector
          kC kB hTarget i hNone e f p hLong
      have hFreshSource : ∀ t : Fin n,
          C.connector t ≠ Sum.inr p := by
        intro t hOld
        exact (hLaterFresh (oldPos i) e p f hp (oldPos t))
          ((hConnector t).trans hOld)
      exact Or.inr ⟨e, f, p, hSource, hFreshSource⟩

end StructuralRamsey.Girth.OrderOneData

import Girth.TrainShortOnlyPlanGlobal

/-!
# Pull bottom supremeness back across forest-leaf replacements

At the bottom coordinate each wagon contains one physical edge, so a long
replacement is impossible.  When a legal relabelling retains the connector
word and introduces no new designated occurrences, a later supreme copy
therefore supplies short witnesses in the original cycle.  The existing
short-only assembly theorem constructs their globally legal simultaneous
plan.  This is the pullback needed after deleting one leaf of a forest.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Distinct physical edges cannot form a long piece in a one-edge wagon. -/
theorem BigCycle.longValid_false_of_parent_injective
    (hBottom : Function.Injective D.parent)
    {n : ℕ} (C : D.BigCycle n) (k j : Fin n)
    (e : E) (w : P) (f : E) :
    ¬ C.LongValid D k j e w f := by
  rintro ⟨_, _, _, _, _, _, hef, hep, hfp, _⟩
  exact hef (hBottom (hep.trans hfp.symm))

/-- Bottom supremeness pulls back across a legal relabelling with the same
connectors and no newly designated occurrences.  Repeated occurrences of the
supreme label are retained by the existing short-only plan constructor. -/
theorem BigCycle.bottom_hasSupremeAt_pullback_sameConnectors
    (hBottom : Function.Injective D.parent)
    {n : ℕ} (C B : D.BigCycle n)
    (hAccept : C.Acceptable)
    (hConnector : ∀ j : Fin n, B.connector j = C.connector j)
    (hDesignated : ∀ j : Fin n, D.designated (B.label j) →
      C.label j = B.label j)
    (k : Fin n) (hSupreme : B.HasSupremeAt D k) :
    C.HasSupremeAt D k := by
  obtain ⟨hk, pieces, hValid, _⟩ := hSupreme
  have hkLabel : C.label k = B.label k := hDesignated k hk
  have hkSource : D.designated (C.label k) := by rw [hkLabel]; exact hk
  apply C.hasSupremeAt_of_all_shortValid D hAccept k hkSource
  intro j hj
  have hjTarget : B.label j ≠ B.label k := by
    intro hEq
    have hjDes : D.designated (B.label j) := by rw [hEq]; exact hk
    exact hj ((hDesignated j hjDes).trans (hEq.trans hkLabel.symm))
  have hPiece := (hValid j).2 hjTarget
  cases hp : pieces j with
  | keep =>
      have hFalse : False := by simpa only [hp] using hPiece
      exact hFalse.elim
  | short e =>
      have hShort : B.ShortValid D k j e := by simpa only [hp] using hPiece
      refine ⟨e, ?_⟩
      simpa only [BigCycle.ShortValid, hConnector, ← hkLabel] using hShort
  | long e w f =>
      have hLong : B.LongValid D k j e w f := by simpa only [hp] using hPiece
      exact (B.longValid_false_of_parent_injective D hBottom k j e w f hLong).elim

/-- The unindexed form used by induction on the supporting forest. -/
theorem BigCycle.bottom_hasSimultaneousSupreme_pullback_sameConnectors
    (hBottom : Function.Injective D.parent)
    {n : ℕ} (C B : D.BigCycle n)
    (hAccept : C.Acceptable)
    (hConnector : ∀ j : Fin n, B.connector j = C.connector j)
    (hDesignated : ∀ j : Fin n, D.designated (B.label j) →
      C.label j = B.label j)
    (hSupreme : B.HasSimultaneousSupreme) :
    C.HasSimultaneousSupreme := by
  obtain ⟨k, hk, pieces, hValid, hGlobal⟩ := hSupreme
  exact C.hasSimultaneousSupreme_of_hasSupremeAt D k
    (C.bottom_hasSupremeAt_pullback_sameConnectors D hBottom B hAccept
      hConnector hDesignated k ⟨hk, pieces, hValid, hGlobal⟩)

end StructuralRamsey.Girth.OrderOneData

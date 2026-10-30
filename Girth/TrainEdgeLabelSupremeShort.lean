import Girth.TrainSimultaneousSupreme

/-!
# A physical-edge occurrence cannot have a long supreme replacement

A long replacement requires its two source boundary vertices not to
share any ambient support edge. But when the source occurrence is
itself an actual edge label, that source edge meets both boundary
connectors. Thus if a different designated label is supreme, the
PlanValid replacement at this source occurrence MUST be short.

This is a purely literal BigCycle theorem, valid including cyclic
wrap and the two-occurrence case. It assumes the real PlanValid
condition and does not postulate a supreme label or an output cycle.
No appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- At an actual physical-edge source occurrence, any replacement
from a different designated supreme label is short, never long:
the source edge itself contradicts the no-pair-edge condition
required by LongValid. -/
theorem BigCycle.supreme_piece_short_of_edge_label
    {n : ℕ} (C : D.BigCycle n)
    (target source : Fin n) (i : I) (b : E)
    (hTarget : C.label target = Sum.inl i)
    (hSource : C.label source = Sum.inr b)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D target pieces) :
    ∃ edge : E, pieces source = .short edge ∧
      C.ShortValid D target source edge := by
  have hDifferent : C.label source ≠ C.label target := by
    rw [hSource, hTarget]
    intro h
    cases h
  have hPiece := (hPlan source).2 hDifferent
  cases hp : pieces source with
  | keep =>
      exact False.elim (by simpa only [hp] using hPiece)
  | short edge =>
      exact ⟨edge, hp, by simpa only [hp] using hPiece⟩
  | long e w f =>
      have hLong : C.LongValid D target source e w f := by
        simpa only [hp] using hPiece
      obtain ⟨x, y, hLeft, hRight, _he, _hf, _hne, _hParentE,
          _hParentF, _hx, _hy, hNoPair⟩ := hLong
      have hPrevInc : D.Incident (Sum.inr b)
          (C.connector (trainCyclicPred source)) := by
        have h := C.right_incident (trainCyclicPred source)
        rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two source,
          hSource] at h
        exact h
      have hNextInc : D.Incident (Sum.inr b) (C.connector source) := by
        have h := C.left_incident source
        rw [hSource] at h
        exact h
      rw [hLeft] at hPrevInc
      rw [hRight] at hNextInc
      change x ∈ D.edgeCarrier b at hPrevInc
      change y ∈ D.edgeCarrier b at hNextInc
      exact False.elim (hNoPair ⟨b, hPrevInc, hNextInc⟩)

/-- The indexed supreme plan, when it exists, has a short piece
at every actual edge-labelled occurrence different from its
chosen designated label. The PlanProducesBigCycle witness is
retained unchanged: no conversion to an illegitimate local-only
notion of supremeness. -/
theorem BigCycle.hasSupremeAt_short_of_edge_label
    {n : ℕ} (C : D.BigCycle n)
    (target source : Fin n) (i : I) (b : E)
    (hTarget : C.label target = Sum.inl i)
    (hSource : C.label source = Sum.inr b)
    (hSupreme : C.HasSupremeAt D target) :
    ∃ (pieces : Fin n → TrainSupremePiece E P) (edge : E),
      C.PlanValid D target pieces ∧
      C.PlanProducesBigCycle D pieces ∧
      pieces source = .short edge ∧
      C.ShortValid D target source edge := by
  obtain ⟨_hDesignated, pieces, hPlan, hProduces⟩ := hSupreme
  obtain ⟨edge, hShortPiece, hShortValid⟩ :=
    C.supreme_piece_short_of_edge_label
      D target source i b hTarget hSource pieces hPlan
  exact ⟨pieces, edge, hPlan, hProduces, hShortPiece, hShortValid⟩

end StructuralRamsey.Girth.OrderOneData

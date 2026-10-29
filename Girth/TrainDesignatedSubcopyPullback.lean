import Girth.TrainDesignatedSubcopyLocalSupreme
import Girth.TrainArbitraryLegalReplacementComplete

/-!
# Circulation: pull a localized target supreme plan back to the original cycle

Once the scattering construction supplies its actual replacement cycle in
one component, the existing arbitrary-replacement theorem and the checked
local component theorem compose directly. Both cycles live in the same
target-labelled ambient system, with every ambient edge and wagon retained.

The literal replacement word, its long-piece geometry, the retained target
and the component confinement remain explicit inputs. This file does not
construct that replacement or infer confinement from an old parent label.
It closes the subsequent supremeness pullback at every source length,
including the length-two/order-one boundary case.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A literal geometrically valid replacement localized in one component
makes that component's target supreme in the original cycle. The conclusion
retains an original occurrence of the exact target label, not merely its
old designated parent.

The retained target in `B` supplies the order-one designated-retention
condition. Acceptability of `B` is derived from the literal replacement,
rather than assumed or inferred from its local pieces alone. -/
theorem BigCycle.supreme_of_localized_component_replacement
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces)
    (target : I) (G : D.ComponentTargetGeometry target)
    (k : Fin m) (hk : B.label k = Sum.inl target)
    (hLabels : ∀ j : Fin m, B.label j = Sum.inl target ∨
      ∃ e, B.label j = Sum.inr e ∧ e ∈ G.componentEdges) :
    ∃ kC : Fin n, C.label kC = Sum.inl target ∧ C.HasSupremeAt D kC := by
  have hRetain : C.twiceOrder = 2 →
      ∃ j : Fin m, D.designated (B.label j) := by
    intro _
    refine ⟨k, ?_⟩
    rw [hk]
    change True
    trivial
  obtain ⟨hBAccept, _hOrder, hPullback⟩ :=
    C.arbitrary_legal_replacement_all_conclusions
      D B hAccept hLinear pieces hGeom hWord hRetain
  have hBSupreme := B.hasSupremeAt_of_component_target
    D hBAccept target G k hk hLabels
  obtain ⟨kC, hLabel, hSupreme⟩ := hPullback k hBSupreme
  exact ⟨kC, hLabel.trans hk, hSupreme⟩

end StructuralRamsey.Girth.OrderOneData

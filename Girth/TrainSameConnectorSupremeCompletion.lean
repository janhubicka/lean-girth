import Girth.TrainSameConnectorSupremeTransfer
import Girth.TrainOptionalFreshnessConverse

set_option autoImplicit false
set_option Elab.async false

/-!
# Automatic full supremeness pullback through a literal same-connector step

A geometric short replacement keeps every cyclic connector at its
original position. An already proved theorem transports the complete
chosen supreme plan BACK from such a replacement, provided the later
long pieces have fresh wagon labels. The separate converse-Nodup
theorem proves that this freshness is automatic whenever a later
supreme plan includes its genuine PlanProducesBigCycle witness.

This module composes those two kernel facts. It no longer assumes
freshness or a chosen designated label in the later cycle: the
HasSimultaneousSupreme witness supplies both, and exact designated
label provenance is supplied by the literal first-result word.

The theorem only transfers an EXISTING supreme cycle through an
ACTUAL same-connector, literal-word step. It does not assert that
every positive-cut reduced witness has a valid short replacement,
or construct a rank-decreasing next cycle. Those remain the
geometric part of Track D. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- An already supreme later cycle pulls the ACTUAL chosen designated
label back to an unchanged original source label. Freshness of long
pieces is automatically derived from its global output BigCycle. -/
theorem BigCycle.hasSupremeAt_of_literal_sameConnector_replacement
    {n : ℕ} (C B : D.BigCycle n)
    (hAccept : C.Acceptable)
    (hLinear : D.LinearPretrain)
    (hConn : ∀ i : Fin n, B.connector i = C.connector i)
    (first : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun i : Fin n =>
      (B.label i, B.connector i)) = C.resultWord D first)
    (kB : Fin n) (hAt : B.HasSupremeAt D kB) :
    ∃ kC : Fin n,
      B.label kB = C.label kC ∧ C.HasSupremeAt D kC := by
  obtain ⟨later, hPlanLater, _hProduces, hFresh⟩ :=
    B.freshness_of_hasSupremeAt D kB hAt
  exact C.supreme_plan_transfer_literal_sameConnectors
    D B hAccept hLinear hConn first hWord kB hAt.1
    later hPlanLater hFresh

/-- Full globally valid simultaneous supremeness pulls back from
an actual literal same-connector replacement. Both the later chosen
designated occurrence and freshness of all later long wagons are
derived; neither is an external hypothesis. This handles arbitrary
finite lengths, including order-one cycles. -/
theorem BigCycle.supreme_of_literal_sameConnector_replacement
    {n : ℕ} (C B : D.BigCycle n)
    (hAccept : C.Acceptable)
    (hLinear : D.LinearPretrain)
    (hConn : ∀ i : Fin n, B.connector i = C.connector i)
    (first : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun i : Fin n =>
      (B.label i, B.connector i)) = C.resultWord D first)
    (hSupreme : B.HasSimultaneousSupreme) :
    C.HasSimultaneousSupreme := by
  obtain ⟨kB, hkB, pieces, hPlan, hProduces⟩ := hSupreme
  have hAt : B.HasSupremeAt D kB :=
    ⟨hkB, pieces, hPlan, hProduces⟩
  obtain ⟨kC, _hSameLabel, hSupC⟩ :=
    C.hasSupremeAt_of_literal_sameConnector_replacement
      D B hAccept hLinear hConn first hWord kB hAt
  exact C.hasSimultaneousSupreme_of_hasSupremeAt D kC hSupC

end StructuralRamsey.Girth.OrderOneData

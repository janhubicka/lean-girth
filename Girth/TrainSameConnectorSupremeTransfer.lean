import Girth.TrainArbitraryGeometricA2
import Girth.TrainStrictPlanComplete

/-!
# Circulation: compose supreme plans through same-connector relabellings

The easiest non-strict case of admissible-replacement composition is a
first replacement that changes only occurrence labels and keeps EVERY
connector at exactly its original cyclic index.

If the output's chosen supreme label already occurs in the source, and
no new occurrence of that label was created, copy its supreme pieces
back to the source on all differently labelled occurrences. On source
occurrences of the selected label, simply keep the old label. Local
ShortValid/LongValid transports verbatim, because both source and
output use the same connector sequence and physical pretrain.

A fresh later long wagon stays fresh against the source connectors.
The checked all-length strict-plan theorem then assembles a genuine
supreme output from the source, proving the desired local composition.

This is a reusable short-only composition INTERFACE. It does not yet
derive the necessary label-provenance and freshness inputs from a
specific first short-only replacement, nor address first long pieces.
No appendix theorem or new axiom is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Short validity transports from a relabelled cycle to the source
whenever both connector sequences agree and the chosen target
designated labels are the same physical label. -/
theorem BigCycle.shortValid_transport_sameConnectors
    {n : ℕ} (C B : D.BigCycle n)
    (hConn : ∀ i : Fin n, B.connector i = C.connector i)
    (kC kB i : Fin n)
    (hTarget : B.label kB = C.label kC)
    (e : E)
    (hShort : B.ShortValid D kB i e) :
    C.ShortValid D kC i e := by
  rcases hShort with ⟨he, hBefore, hHere⟩
  exact ⟨by simpa only [hTarget] using he,
    by simpa only [hConn] using hBefore,
    by simpa only [hConn] using hHere⟩

/-- The same transport for genuine long pieces: both original
connector vertices and all physical wagon/nonedge data agree. -/
theorem BigCycle.longValid_transport_sameConnectors
    {n : ℕ} (C B : D.BigCycle n)
    (hConn : ∀ i : Fin n, B.connector i = C.connector i)
    (kC kB i : Fin n)
    (hTarget : B.label kB = C.label kC)
    (e f : E) (p : P)
    (hLong : B.LongValid D kB i e p f) :
    C.LongValid D kC i e p f := by
  obtain ⟨x, y, hBefore, hHere, he, hf, hne,
    hpe, hpf, hxe, hyf, hNoPair⟩ := hLong
  exact ⟨x, y,
    by simpa only [hConn] using hBefore,
    by simpa only [hConn] using hHere,
    by simpa only [hTarget] using he,
    by simpa only [hTarget] using hf,
    hne, hpe, hpf, hxe, hyf, hNoPair⟩

/-- Pull back the actual strict supreme plan of a relabelled
same-connector cycle. There is no extra precompactness, geometry
or output acceptability assumption. -/
theorem BigCycle.supreme_plan_transfer_sameConnectors
    {n : ℕ} (C B : D.BigCycle n)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (hConn : ∀ i : Fin n, B.connector i = C.connector i)
    (kC kB : Fin n)
    (hTarget : B.label kB = C.label kC)
    (hDes : D.designated (B.label kB))
    (hProvenance : ∀ i : Fin n,
      B.label i = B.label kB →
      C.label i = C.label kC)
    (later : Fin n → TrainSupremePiece E P)
    (hPlan : B.PlanValid D kB later)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      later i = .long e p f →
      ∀ t : Fin n, B.connector t ≠ Sum.inr p) :
    C.HasSupremeAt D kC := by
  let composed : Fin n → TrainSupremePiece E P :=
    fun i => if h : C.label i = C.label kC then .keep else later i
  have hkC : D.designated (C.label kC) := by
    simpa only [← hTarget] using hDes
  have hComposed : C.PlanValid D kC composed := by
    intro i
    constructor
    · intro hEq
      simp [composed, hEq]
    · intro hNe
      have hLaterNe : B.label i ≠ B.label kB := by
        intro hEq
        exact hNe (hProvenance i hEq)
      have hv := (hPlan i).2 hLaterNe
      cases hp : later i with
      | keep =>
          simp [hp] at hv
      | short e =>
          have hShort : B.ShortValid D kB i e := by
            simpa [hp] using hv
          have hTransferred :=
            C.shortValid_transport_sameConnectors
              D B hConn kC kB i hTarget e hShort
          simpa [composed, hNe, hp] using hTransferred
      | long e p f =>
          have hLong : B.LongValid D kB i e p f := by
            simpa [hp] using hv
          have hTransferred :=
            C.longValid_transport_sameConnectors
              D B hConn kC kB i hTarget e f p hLong
          simpa [composed, hNe, hp] using hTransferred
  have hFreshC :
      ∀ (i : Fin n) (e : E) (p : P) (f : E),
        composed i = .long e p f →
        ∀ t : Fin n, C.connector t ≠ Sum.inr p := by
    intro i e p f hp t
    by_cases hEq : C.label i = C.label kC
    · simp [composed, hEq] at hp
    · have hLater : later i = .long e p f := by
        simpa [composed, hEq] using hp
      simpa only [hConn] using (hFresh i e p f hLater t)
  obtain ⟨m, Out, _hOutAccept, _hOrder, hWord⟩ :=
    C.planProducesAcceptableOrder_all_lengths
      D hAccept hLinear kC hkC composed hComposed hFreshC
  exact ⟨hkC, composed, hComposed, m, Out, hWord⟩

end StructuralRamsey.Girth.OrderOneData

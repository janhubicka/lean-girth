import Girth.TrainSupremePlanTransport
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Circulation Path A: transport one OLD local replacement piece

A literal standard physical embedding maps all four incidence sorts:
vertices, actual A-support edges, designated labels, and wagon
classes. It already transports a WHOLE chosen supreme plan when the
source BigCycle is itself mapped from one standard.

The original length-two obstruction is harder: its two source labels
can belong to different standards, so the WHOLE source BigCycle need
not be the image of an old one-standard cycle. Only its chosen
original designated target and TWO connector endpoints are known
to lie in that standard.

These two theorems map one genuine old local ShortPiece/LongPiece
directly to the output endpoints, WITHOUT postulating a source
BigCycle for the other label. The long proof uses the real
no-new-ambient-pair reflection of A-strong attachment, and it
preserves the exact physical wagon class and distinct edges.

This does NOT produce an old local piece from old system girth:
that separate probe/ownership obligation remains necessary.
No appendix or manuscript change.
-/

namespace StructuralRamsey.Girth.OrderOneData
universe v w

namespace LiteralPhysicalMap

variable {V E I P : Type v} {V' E' I' P' : Type w}
variable {D : OrderOneData V E I P}
variable {H : OrderOneData V' E' I' P'}
variable (M : LiteralPhysicalMap D H)

/-- A genuine old short edge belonging to an OLD original
designated label transports to a physical output short through
the two mapped endpoint connectors. No old source cycle is needed. -/
theorem shortPiece_map_local
    (a : I ⊕ E) (q r : V ⊕ P)
    (h : D.ShortPiece a q r) :
    H.ShortPiece (M.mapLabel a)
      (M.mapConnector q) (M.mapConnector r) := by
  obtain ⟨edge, hMem, hQ, hR⟩ := h
  refine ⟨M.edge edge, ?_, ?_, ?_⟩
  · exact M.source_edge a edge hMem
  · have hh := M.incident (Sum.inr edge) q hQ
    change H.Incident (Sum.inr (M.edge edge)) (M.mapConnector q) at hh
    exact hh
  · have hh := M.incident (Sum.inr edge) r hR
    change H.Incident (Sum.inr (M.edge edge)) (M.mapConnector r) at hh
    exact hh

/-- A genuine old two-edge common-wagon long piece belonging to
the ORIGINAL old designated label transports to the output with
the SAME exact wagon embedding, distinct physical edges, and
genuine no-new-pair condition. No whole-source-cycle image is
assumed, only the two mapped endpoint connectors. -/
theorem longPiece_map_local
    (a : I ⊕ E) (q r : V ⊕ P)
    (h : D.LongPiece a q r) :
    H.LongPiece (M.mapLabel a)
      (M.mapConnector q) (M.mapConnector r) := by
  obtain ⟨x, y, p, e, f, hQ, hR, hE, hF,
    hNe, hPE, hPF, hXE, hYF, hNoPair⟩ := h
  have hXY : x ≠ y := by
    intro h
    subst y
    exact hNoPair ⟨e, hXE, hXE⟩
  refine ⟨M.vertex x, M.vertex y, M.wagon p,
    M.edge e, M.edge f, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hQ]
    rfl
  · rw [hR]
    rfl
  · exact M.source_edge a e hE
  · exact M.source_edge a f hF
  · intro heq
    exact hNe (M.edge.injective heq)
  · exact M.parent e |>.trans (congrArg M.wagon hPE)
  · exact M.parent f |>.trans (congrArg M.wagon hPF)
  · have hh := M.incident (Sum.inr e) (Sum.inl x)
      (by exact hXE)
    simpa [Incident, carrier] using hh
  · have hh := M.incident (Sum.inr f) (Sum.inl y)
      (by exact hYF)
    simpa [Incident, carrier] using hh
  · intro hPair
    exact hNoPair (M.no_new_pair x y hXY hPair)

/-- Two genuine old standard support edges have the same OLD wagon
whenever their real output physical images have the same output
wagon. This uses the INJECTIVE actual standard wagon embedding,
not the false claim that any output wagon has one canonical
unlabelled old representative. -/
theorem source_parent_eq_of_output_parent_eq
    (a b : E)
    (h : H.parent (M.edge a) = H.parent (M.edge b)) :
    D.parent a = D.parent b := by
  apply M.wagon.injective
  calc
    M.wagon (D.parent a) = H.parent (M.edge a) :=
      (M.parent a).symm
    _ = H.parent (M.edge b) := h
    _ = M.wagon (D.parent b) := M.parent b

/-- The disjunction required by the ORIGINAL source length-two
local-to-global theorem transports under the same standard map. -/
theorem localPiece_map
    (a : I ⊕ E) (q r : V ⊕ P)
    (h : D.ShortPiece a q r ∨ D.LongPiece a q r) :
    H.ShortPiece (M.mapLabel a)
      (M.mapConnector q) (M.mapConnector r) ∨
    H.LongPiece (M.mapLabel a)
      (M.mapConnector q) (M.mapConnector r) := by
  rcases h with hs | hl
  · exact Or.inl (M.shortPiece_map_local a q r hs)
  · exact Or.inr (M.longPiece_map_local a q r hl)

end LiteralPhysicalMap
end StructuralRamsey.Girth.OrderOneData

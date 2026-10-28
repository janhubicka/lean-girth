import Girth.TrainSupremeWordTransport

/-!
# Full simultaneous supremeness transfers under physical incidence maps

A literal physical map preserves genuine source edge membership,
physical connector incidence, and old wagon parent classes. Its
injective vertex/edge/label/wagon maps preserve distinguished
occurrence choices. Crucially, the separate no-new-ambient-pair
interface is needed to lift LongValid without creating a new edge
between its distinct boundary vertices.

The previous module checked the GLOBAL simultaneous replacement
word, by actually mapping its witness BigCycle and all short/long
replacement blocks. Here we discharge PlanValid for every position,
including the nonkept ones, then obtain HasSimultaneousSupreme.
No claim about how a specific picture step obtains the morphism;
that is the next physical instantiation. No appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v w
namespace LiteralPhysicalMap

variable {V E I P : Type v} {V' E' I' P' : Type w}
variable {D : OrderOneData V E I P} {H : OrderOneData V' E' I' P'}
variable (M : LiteralPhysicalMap D H)

/-- Exact old short replacement pieces retain their designated
source membership and BOTH physical boundary incidences. -/
theorem shortValid_map {n : ℕ} (C : D.BigCycle n)
    (k j : Fin n) (e : E)
    (hShort : BigCycle.ShortValid D C k j e) :
    BigCycle.ShortValid H (M.mapBigCycle C) k j (M.edge e) := by
  rcases hShort with ⟨hEdge, hLeft, hRight⟩
  refine ⟨?_, ?_, ?_⟩
  · exact M.source_edge (C.label k) e hEdge
  · exact M.incident (Sum.inr e)
      (C.connector (trainCyclicPred j)) hLeft
  · exact M.incident (Sum.inr e) (C.connector j) hRight

/-- Old valid long pieces map to valid long pieces without new
ambient pair edges at their distinct vertex boundaries. In
particular old e != f remains true for real physical edge labels. -/
theorem longValid_map {n : ℕ} (C : D.BigCycle n)
    (k j : Fin n) (e : E) (p : P) (f : E)
    (hLong : BigCycle.LongValid D C k j e p f) :
    BigCycle.LongValid H (M.mapBigCycle C) k j
      (M.edge e) (M.wagon p) (M.edge f) := by
  obtain ⟨x, y, hLeft, hRight, he, hf, hne, hep, hfp, hx, hy, hNoPair⟩ := hLong
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hNoPair ⟨e, hx, hx⟩
  refine ⟨M.vertex x, M.vertex y, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · change M.mapConnector (C.connector (trainCyclicPred j)) =
        Sum.inl (M.vertex x)
    rw [hLeft]
    rfl
  · change M.mapConnector (C.connector j) = Sum.inl (M.vertex y)
    rw [hRight]
    rfl
  · exact M.source_edge (C.label k) e he
  · exact M.source_edge (C.label k) f hf
  · exact fun h => hne (M.edge.injective h)
  · simpa [M.parent] using congrArg M.wagon hep
  · simpa [M.parent] using congrArg M.wagon hfp
  · have hInc := M.incident (Sum.inr e) (Sum.inl x) hx
    exact hInc
  · have hInc := M.incident (Sum.inr f) (Sum.inl y) hy
    exact hInc
  · intro hNew
    exact hNoPair (M.no_new_pair x y hxy hNew)

/-- The entire replacement plan stays locally valid; no occurrence
of the selected supreme label is silently replaced, because its
literal selected label map is injective. -/
theorem planValid_map {n : ℕ} (C : D.BigCycle n)
    (k : Fin n) (pieces : Fin n → TrainSupremePiece E P)
    (hValid : BigCycle.PlanValid D C k pieces) :
    BigCycle.PlanValid H (M.mapBigCycle C) k
      (fun j => M.mapPiece (pieces j)) := by
  intro j
  constructor
  · intro hSame
    have hOld : C.label j = C.label k :=
      M.mapLabel_injective hSame
    have hKeep := (hValid j).1 hOld
    simpa [hKeep, LiteralPhysicalMap.mapPiece]
  · intro hOther
    have hOld : C.label j ≠ C.label k := by
      intro hEq
      exact hOther (congrArg M.mapLabel hEq)
    have hPiece := (hValid j).2 hOld
    cases hp : pieces j with
    | keep =>
        simp [hp] at hPiece
    | short e =>
        have hs : BigCycle.ShortValid D C k j e := by
          simpa only [hp] using hPiece
        simpa [hp, LiteralPhysicalMap.mapPiece] using
          M.shortValid_map C k j e hs
    | long e p f =>
        have hl : BigCycle.LongValid D C k j e p f := by
          simpa only [hp] using hPiece
        simpa [hp, LiteralPhysicalMap.mapPiece] using
          M.longValid_map C k j e p f hl

/-- FULL global simultaneous supreme replacement plans transfer
through a literal physical map, not merely the existence of
short/long pieces. The output witness is a genuine BigCycle whose
flattened word is exactly the physical image of the old word. -/
theorem hasSimultaneousSupreme_map {n : ℕ} (C : D.BigCycle n)
    (h : C.HasSimultaneousSupreme) :
    (M.mapBigCycle C).HasSimultaneousSupreme := by
  obtain ⟨k, hk, pieces, hLocal, hGlobal⟩ := h
  have hk' : H.designated ((M.mapBigCycle C).label k) := by
    cases hLab : C.label k with
    | inl i =>
        change H.designated (M.mapLabel (C.label k))
        rw [hLab]
        trivial
    | inr e =>
        simp [hLab, OrderOneData.designated] at hk
  exact ⟨k, hk',
    (fun j => M.mapPiece (pieces j)),
    M.planValid_map C k pieces hLocal,
    M.planProduces_map C pieces hGlobal⟩

end LiteralPhysicalMap
end StructuralRamsey.Girth.OrderOneData

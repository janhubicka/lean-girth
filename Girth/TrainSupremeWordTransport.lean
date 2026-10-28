import Girth.TrainSimultaneousSupreme
import Mathlib.Tactic

/-!
# Global simultaneous-replacement words are functorial under physical maps

A literal physical map is injective on ALL four sorts (vertices,
ambient edge labels, designated labels, wagon labels), preserves
literal incidence, membership of the selected supreme copy's
A-support edges and the parent of every actual edge. It also
reflects pair edges between DISTINCT vertices, the freshness
condition for long pieces.

This module first proves the essential GLOBAL interface: a genuine
source BigCycle and any legal output replacement BigCycle map to
genuine target BigCycles; the flattened simultaneous replacement
word COMMUTES with the physical maps. Thus PlanProducesBigCycle is
transported as a theorem, not replaced with a list of locally valid
pieces. Further local ShortValid/LongValid and indexed supremeness
are assembled in a separate module.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v w

/-- A genuine embedding of the labelled physical incidence system.
The injected *edge labels* name actual support edges, rather than
arbitrary embeddings that may have the same carrier. -/
structure LiteralPhysicalMap
    {V E I P : Type v} {V' E' I' P' : Type w}
    (D : OrderOneData V E I P) (H : OrderOneData V' E' I' P') where
  vertex : V ↪ V'
  edge : E ↪ E'
  designated : I ↪ I'
  wagon : P ↪ P'
  incident : ∀ (a : I ⊕ E) (q : V ⊕ P),
    D.Incident a q →
      H.Incident (Sum.map designated edge a) (Sum.map vertex wagon q)
  source_edge : ∀ (a : I ⊕ E) (x : E), x ∈ D.edges a →
    edge x ∈ H.edges (Sum.map designated edge a)
  parent : ∀ x : E, H.parent (edge x) = wagon (D.parent x)
  no_new_pair : ∀ x y : V, x ≠ y →
    H.PairEdge (vertex x) (vertex y) → D.PairEdge x y

namespace LiteralPhysicalMap

variable {V E I P : Type v} {V' E' I' P' : Type w}
variable {D : OrderOneData V E I P} {H : OrderOneData V' E' I' P'}
variable (M : LiteralPhysicalMap D H)

def mapLabel (a : I ⊕ E) : I' ⊕ E' :=
  Sum.map M.designated M.edge a

def mapConnector (q : V ⊕ P) : V' ⊕ P' :=
  Sum.map M.vertex M.wagon q

def mapEntry (x : (I ⊕ E) × (V ⊕ P)) :
    (I' ⊕ E') × (V' ⊕ P') :=
  (M.mapLabel x.1, M.mapConnector x.2)

def mapPiece : TrainSupremePiece E P → TrainSupremePiece E' P'
  | .keep => .keep
  | .short e => .short (M.edge e)
  | .long e p f => .long (M.edge e) (M.wagon p) (M.edge f)

theorem mapLabel_injective : Function.Injective M.mapLabel := by
  intro a b h
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          change Sum.inl (M.designated i) =
            Sum.inl (M.designated j) at h
          exact congrArg Sum.inl (M.designated.injective (Sum.inl.inj h))
      | inr j =>
          change Sum.inl (M.designated i) =
            Sum.inr (M.edge j) at h
          cases h
  | inr i =>
      cases b with
      | inl j =>
          change Sum.inr (M.edge i) =
            Sum.inl (M.designated j) at h
          cases h
      | inr j =>
          change Sum.inr (M.edge i) =
            Sum.inr (M.edge j) at h
          exact congrArg Sum.inr (M.edge.injective (Sum.inr.inj h))

theorem mapConnector_injective :
    Function.Injective M.mapConnector := by
  intro a b h
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          change Sum.inl (M.vertex i) = Sum.inl (M.vertex j) at h
          exact congrArg Sum.inl (M.vertex.injective (Sum.inl.inj h))
      | inr j =>
          change Sum.inl (M.vertex i) = Sum.inr (M.wagon j) at h
          cases h
  | inr i =>
      cases b with
      | inl j =>
          change Sum.inr (M.wagon i) = Sum.inl (M.vertex j) at h
          cases h
      | inr j =>
          change Sum.inr (M.wagon i) = Sum.inr (M.wagon j) at h
          exact congrArg Sum.inr (M.wagon.injective (Sum.inr.inj h))

/-- An arbitrary actual source BigCycle has a genuine physical-image
BigCycle with the SAME number of occurrences and the exact source
label and connector maps. -/
def mapBigCycle {n : ℕ} (C : D.BigCycle n) : H.BigCycle n where
  length_ge_two := C.length_ge_two
  label := fun j => M.mapLabel (C.label j)
  connector := fun j => M.mapConnector (C.connector j)
  adjacent_ne := by
    intro j hj
    exact C.adjacent_ne j (M.mapLabel_injective hj)
  connector_injective := by
    intro j k hjk
    exact C.connector_injective (M.mapConnector_injective hjk)
  left_incident := by
    intro j
    exact M.incident (C.label j) (C.connector j) (C.left_incident j)
  right_incident := by
    intro j
    exact M.incident (C.label (cyclicSucc j)) (C.connector j)
      (C.right_incident j)

/-- The literal replacement block of one occurrence commutes with
the physical map. Unlike geometric replacements by another copy,
the original designated label remains exactly identified. -/
theorem pieceWord_map
    {n : ℕ} (C : D.BigCycle n) (j : Fin n)
    (piece : TrainSupremePiece E P) :
    BigCycle.pieceWord H (M.mapBigCycle C) j (M.mapPiece piece) =
      (BigCycle.pieceWord D C j piece).map M.mapEntry := by
  cases piece <;>
    simp [BigCycle.pieceWord, mapBigCycle, mapPiece, mapEntry,
      mapLabel, mapConnector]

/-- Transport of the entire FLATTENED simultaneous replacement word,
including the wagon inserted inside a long piece, not just the
original connector positions. -/
theorem resultWord_map
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) :
    BigCycle.resultWord H (M.mapBigCycle C)
      (fun j => M.mapPiece (pieces j)) =
        (BigCycle.resultWord D C pieces).map M.mapEntry := by
  simp [BigCycle.resultWord, List.map_flatten,
    List.map_ofFn, M.pieceWord_map, Function.comp_def]

/-- Global legality really transfers. The original PlanProduces
witness is a concrete BigCycle, mapped using verified incidence,
injectivity and the exact flattened-word equality. -/
theorem planProduces_map
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (h : BigCycle.PlanProducesBigCycle D C pieces) :
    BigCycle.PlanProducesBigCycle H (M.mapBigCycle C)
      (fun j => M.mapPiece (pieces j)) := by
  obtain ⟨m, B, hWord⟩ := h
  refine ⟨m, M.mapBigCycle B, ?_⟩
  calc
    List.ofFn (fun j : Fin m =>
        ((M.mapBigCycle B).label j, (M.mapBigCycle B).connector j)) =
      (List.ofFn (fun j : Fin m => (B.label j, B.connector j))).map
        M.mapEntry := by
        simp [mapBigCycle, mapEntry, mapLabel, mapConnector,
          List.map_ofFn, Function.comp_def]
    _ = (BigCycle.resultWord D C pieces).map M.mapEntry :=
      congrArg (List.map M.mapEntry) hWord
    _ = BigCycle.resultWord H (M.mapBigCycle C)
        (fun j => M.mapPiece (pieces j)) :=
      (M.resultWord_map C pieces).symm

end LiteralPhysicalMap
end StructuralRamsey.Girth.OrderOneData

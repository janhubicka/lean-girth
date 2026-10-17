import Girth.TrainArbitraryEdgeBoundaryCollision

/-!
# Circulation: adjacent replacement block labels never collide

At a source occurrence, the first or last physical label is either
the retained old label or an actual edge. If it is an edge e,
then e either meets both old boundary connectors (a kept edge or a
short replacement), or its fresh parent wagon contains both old
boundary vertices (a long replacement).

Two consecutive replacement blocks with an equal physical boundary
label would therefore violate the generic three-contact obstruction.
An equal designated boundary label would mean both occurrences were
kept, contradicting original adjacent label distinctness.

This proves the label inequality for arbitrary local geometric
replacement plans, without a selected supreme source target, using
only the original acceptable cycle and n>=3.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Every edge in one valid long piece has a fresh parent wagon
containing the two original source boundary vertices. -/
theorem BigCycle.physical_edge_boundary_of_long
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (i : Fin n) (e f : E) (p : P)
    (hi : pieces i = .long e p f)
    (g : E) (hParent : D.parent g = p) :
    C.PhysicalEdgeBoundary D i g := by
  obtain ⟨x, y, hBefore, hHere, hWx, hWy, _hNoPair⟩ :=
    hGeom i e f p hi
  right
  refine ⟨?_, ?_, ?_⟩
  · rw [hParent]
    exact ⟨x, hBefore, hWx⟩
  · rw [hParent]
    exact ⟨y, hHere, hWy⟩
  · rw [hParent]
    exact hFresh i e p f hi

/-- When the last label of a block is a physical edge, it has one
of the two boundary geometries needed by the collision principle. -/
theorem BigCycle.pieceLast_edge_boundary
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hInc : C.LocalPieceIncidence D pieces)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (i : Fin n) (e : E)
    (hLast : C.pieceLastLabel D (C.label i) (pieces i) = Sum.inr e) :
    C.PhysicalEdgeBoundary D i e := by
  cases hp : pieces i with
  | keep =>
      have hLabel : C.label i = Sum.inr e := by
        simpa [BigCycle.pieceLastLabel, hp] using hLast
      left
      have hLeft := C.right_incident (trainCyclicPred i)
      rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i] at hLeft
      have hRight := C.left_incident i
      rw [hLabel] at hLeft hRight
      exact ⟨hLeft, hRight⟩
  | short f =>
      have heq : f = e := Sum.inr.inj (by
        simpa [BigCycle.pieceLastLabel, hp] using hLast)
      subst e
      left
      simpa [BigCycle.LocalPieceIncidence, hp] using hInc i
  | long f p g =>
      have heq : g = e := Sum.inr.inj (by
        simpa [BigCycle.pieceLastLabel, hp] using hLast)
      subst e
      have hv : f ≠ g ∧
          D.Incident (.inr f) (C.connector (trainCyclicPred i)) ∧
          D.parent f = p ∧ D.parent g = p ∧
          D.Incident (.inr g) (C.connector i) := by
        simpa [BigCycle.LocalPieceIncidence, hp] using hInc i
      exact C.physical_edge_boundary_of_long
        D pieces hGeom hFresh i f g p hp g hv.2.2.2.1

/-- Symmetric characterization for the first physical edge label
of a replacement block. -/
theorem BigCycle.pieceFirst_edge_boundary
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hInc : C.LocalPieceIncidence D pieces)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (i : Fin n) (e : E)
    (hFirst : C.pieceFirstLabel D (C.label i) (pieces i) = Sum.inr e) :
    C.PhysicalEdgeBoundary D i e := by
  cases hp : pieces i with
  | keep =>
      have hLabel : C.label i = Sum.inr e := by
        simpa [BigCycle.pieceFirstLabel, hp] using hFirst
      left
      have hLeft := C.right_incident (trainCyclicPred i)
      rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i] at hLeft
      have hRight := C.left_incident i
      rw [hLabel] at hLeft hRight
      exact ⟨hLeft, hRight⟩
  | short f =>
      have heq : f = e := Sum.inr.inj (by
        simpa [BigCycle.pieceFirstLabel, hp] using hFirst)
      subst e
      left
      simpa [BigCycle.LocalPieceIncidence, hp] using hInc i
  | long f p g =>
      have heq : f = e := Sum.inr.inj (by
        simpa [BigCycle.pieceFirstLabel, hp] using hFirst)
      subst e
      have hv : f ≠ g ∧
          D.Incident (.inr f) (C.connector (trainCyclicPred i)) ∧
          D.parent f = p ∧ D.parent g = p ∧
          D.Incident (.inr g) (C.connector i) := by
        simpa [BigCycle.LocalPieceIncidence, hp] using hInc i
      exact C.physical_edge_boundary_of_long
        D pieces hGeom hFresh i f g p hp f hv.2.2.1

/-- A designated last label occurs only in a kept original block. -/
theorem BigCycle.pieceLast_designated_label
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (i : Fin n) (a : I)
    (h : C.pieceLastLabel D (C.label i) (pieces i) = Sum.inl a) :
    C.label i = Sum.inl a := by
  cases hp : pieces i with
  | keep => simpa [BigCycle.pieceLastLabel, hp] using h
  | short e => cases (show (Sum.inr e : I ⊕ E) = Sum.inl a by
        simpa [BigCycle.pieceLastLabel, hp] using h)
  | long e p f => cases (show (Sum.inr f : I ⊕ E) = Sum.inl a by
        simpa [BigCycle.pieceLastLabel, hp] using h)

/-- Likewise for a designated first label. -/
theorem BigCycle.pieceFirst_designated_label
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (i : Fin n) (a : I)
    (h : C.pieceFirstLabel D (C.label i) (pieces i) = Sum.inl a) :
    C.label i = Sum.inl a := by
  cases hp : pieces i with
  | keep => simpa [BigCycle.pieceFirstLabel, hp] using h
  | short e => cases (show (Sum.inr e : I ⊕ E) = Sum.inl a by
        simpa [BigCycle.pieceFirstLabel, hp] using h)
  | long e p f => cases (show (Sum.inr e : I ⊕ E) = Sum.inl a by
        simpa [BigCycle.pieceFirstLabel, hp] using h)

/-- All adjacent source-block boundary labels of an arbitrary
locally valid replacement are distinct, cyclic wrap included. -/
theorem BigCycle.arbitrary_adjacent_piece_labels_ne
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hInc : C.LocalPieceIncidence D pieces)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (i : Fin n) :
    C.pieceLastLabel D (C.label i) (pieces i) ≠
      C.pieceFirstLabel D (C.label (cyclicSucc i))
        (pieces (cyclicSucc i)) := by
  intro hSame
  cases hLast : C.pieceLastLabel D (C.label i) (pieces i) with
  | inl a =>
      have hFirst :
          C.pieceFirstLabel D (C.label (cyclicSucc i))
            (pieces (cyclicSucc i)) = Sum.inl a :=
        hSame.symm.trans hLast
      have hA := C.pieceLast_designated_label D pieces i a hLast
      have hB := C.pieceFirst_designated_label
        D pieces (cyclicSucc i) a hFirst
      exact C.adjacent_ne i (hA.trans hB.symm)
  | inr e =>
      have hFirst :
          C.pieceFirstLabel D (C.label (cyclicSucc i))
            (pieces (cyclicSucc i)) = Sum.inr e :=
        hSame.symm.trans hLast
      exact C.physical_edge_boundary_ne_next D hAccept hn i e
        (C.pieceLast_edge_boundary D pieces
          hInc hGeom hFresh i e hLast)
        (C.pieceFirst_edge_boundary D pieces
          hInc hGeom hFresh (cyclicSucc i) e hFirst)

end StructuralRamsey.Girth.OrderOneData

import Girth.TrainFillingPrivateExtension
import Mathlib.Tactic
import Mathlib.Order.WithBot

set_option Elab.async false

/-!
# Finite insertion anchors for compatible private first-wagon orders

Let V be the finite ordered old target vertices and X the ordered
uniform template. For a first wagon p, the genuine private extension
uses the coordinate embedding of its old carrier in X.

For each x in X, let successors(p,x) be the old vertices of p
whose X-coordinate lies STRICTLY after x. Define anchor(p,x)
as their minimum, or top when the set is empty.

The elementary key facts are proved from the actual coordinates:
(1) anchor is monotone in x, without an order assumption on old
    coordinates;
(2) x < coordinate_p(v) implies anchor(p,x) ≤ v;
(3) coordinate_p(v) < x implies v < anchor(p,x), provided
    coordinate_p is genuinely strictly monotone.

These are the precise finite-minimum facts needed to construct one
global order on all private positions, placing them before their
anchor old vertex (or after all old vertices at top). This module
does not yet assert the complete simultaneous order extension.
-/

namespace StructuralRamsey.Girth.PrivateWagonInput

universe v
variable {V P X : Type v}
variable (U : PrivateWagonInput V P X)
variable [LinearOrder V] [Fintype V] [LinearOrder X]

/-- Old p-vertices strictly following x in the local ordered X copy. -/
noncomputable def successorOldVertices (p : P) (x : X) : Finset V := by
  classical
  exact Finset.univ.filter
    (fun v : V => ∃ hv : v ∈ U.oldCarrier p,
      x < U.coordinate p ⟨v, hv⟩)

theorem mem_successorOldVertices (p : P) (x : X) (v : V) :
    v ∈ U.successorOldVertices p x ↔
      ∃ hv : v ∈ U.oldCarrier p,
        x < U.coordinate p ⟨v, hv⟩ := by
  classical
  simp [successorOldVertices]

/-- Minimum old successor in the global V-order; top if no such
successor exists. No arbitrary default old vertex is chosen. -/
noncomputable def insertionAnchor (p : P) (x : X) : WithTop V :=
  (U.successorOldVertices p x).inf (fun v => (v : WithTop V))

/-- The successor set only shrinks as a local X position moves right,
so its minimum can only move right. -/
theorem insertionAnchor_mono (p : P) {x y : X} (hxy : x ≤ y) :
    U.insertionAnchor p x ≤ U.insertionAnchor p y := by
  change (U.successorOldVertices p x).inf
      (fun v : V => (v : WithTop V)) ≤
    (U.successorOldVertices p y).inf
      (fun v : V => (v : WithTop V))
  apply Finset.inf_mono
  intro v hv
  obtain ⟨hOld, hY⟩ :=
    (U.mem_successorOldVertices p y v).mp hv
  exact (U.mem_successorOldVertices p x v).mpr
    ⟨hOld, lt_of_le_of_lt hxy hY⟩

/-- A private local position lying before an old wagon vertex is
inserted no later than that old vertex. -/
theorem insertionAnchor_le_old (p : P) (x : X)
    (z : {v : V // v ∈ U.oldCarrier p})
    (hx : x < U.coordinate p z) :
    U.insertionAnchor p x ≤ (z.1 : WithTop V) := by
  change (U.successorOldVertices p x).inf
    (fun v : V => (v : WithTop V)) ≤ (z.1 : WithTop V)
  apply Finset.inf_le
  exact (U.mem_successorOldVertices p x z.1).mpr
    ⟨z.2, hx⟩

/-- A private local position lying after an old wagon vertex is
inserted strictly after that old vertex. This is where the original
coordinate map's within-predicate order preservation is essential. -/
theorem old_lt_insertionAnchor
    (hCoord : ∀ p : P, StrictMono (U.coordinate p))
    (p : P) (z : {v : V // v ∈ U.oldCarrier p}) (x : X)
    (hz : U.coordinate p z < x) :
    (z.1 : WithTop V) < U.insertionAnchor p x := by
  change (z.1 : WithTop V) <
    (U.successorOldVertices p x).inf
      (fun v : V => (v : WithTop V))
  apply (Finset.lt_inf_iff (WithTop.coe_lt_top z.1)).mpr
  intro v hv
  obtain ⟨hOld, hAfter⟩ :=
    (U.mem_successorOldVertices p x v).mp hv
  have hX : U.coordinate p z <
      U.coordinate p (⟨v, hOld⟩ : {v : V // v ∈ U.oldCarrier p}) :=
    lt_trans hz hAfter
  have hV : z.1 < v := by
    by_contra h
    have hle : v ≤ z.1 := le_of_not_gt h
    have hle' :
        (⟨v, hOld⟩ : {v : V // v ∈ U.oldCarrier p}) ≤ z := hle
    have hBad : U.coordinate p (⟨v, hOld⟩ :
        {v : V // v ∈ U.oldCarrier p}) ≤ U.coordinate p z :=
      (hCoord p).monotone hle'
    exact (not_le_of_gt hX) hBad
  exact WithTop.coe_lt_coe.mpr hV

end StructuralRamsey.Girth.PrivateWagonInput

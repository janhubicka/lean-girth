import Girth.TrainShortOnlyPlanGlobal
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# A length-two vertex-pair source is globally supreme from selected strength

The genuine attached output cannot be assumed to have FullSystemGirthGT:
that is what the forest-partite proof is trying to establish. Instead
use the ACTUAL selected-copy strongness on physical A-edges. If an
ambient edge contains the two distinct vertex connectors of a two-
occurrence acceptable source, then any designated label containing both
vertices must own the entire physical edge.

This gives an actual ShortValid at the opposite occurrence. The already
verified short-only plan theorem assembles it into a globally legal
HasSimultaneousSupreme. No output full-system bound, witness reduced
supreme, invented source B-label, edge pruning, or appendix result.

This theorem is a generic physical-source kernel. Instantiating its
A-strongness premise in the actual selected output is separate.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A genuine vertex-vertex two-occurrence source has full simultaneous
supremeness from a physical pair edge, designated occurrence, and the
literal selected-copy pair-edge closure that strongness supplies. -/
theorem BigCycle.two_vertex_pairEdge_supreme_of_selectedStrong
    (Z : D.BigCycle 2) (hAccept : Z.Acceptable)
    (x y : V)
    (hx : Z.connector (0 : Fin 2) = Sum.inl x)
    (hy : Z.connector (1 : Fin 2) = Sum.inl y)
    (b : E) (hbx : x ∈ D.edgeCarrier b)
    (hby : y ∈ D.edgeCarrier b)
    (hStrong : ∀ (i : I) (edge : E) (u v : V),
      u ≠ v →
      u ∈ D.copyCarrier i → v ∈ D.copyCarrier i →
      u ∈ D.edgeCarrier edge → v ∈ D.edgeCarrier edge →
      edge ∈ D.copyEdges i)
    (hSome : ∃ k : Fin 2, D.designated (Z.label k)) :
    Z.HasSimultaneousSupreme := by
  have hxy : x ≠ y := by
    intro h
    have hEq : Z.connector (0 : Fin 2) = Z.connector (1 : Fin 2) := by
      calc
        Z.connector (0 : Fin 2) = Sum.inl x := hx
        _ = Sum.inl y := by rw [h]
        _ = Z.connector (1 : Fin 2) := hy.symm
    exact (by decide : (0 : Fin 2) ≠ 1) (Z.connector_injective hEq)
  have hBoundary (j : Fin 2) :
      D.Incident (Sum.inr b) (Z.connector j) := by
    fin_cases j
    · simpa [hx, OrderOneData.Incident, OrderOneData.carrier] using hbx
    · simpa [hy, OrderOneData.Incident, OrderOneData.carrier] using hby
  have hLabelVertices (k : Fin 2) (i : I)
      (hLabel : Z.label k = Sum.inl i) :
      x ∈ D.copyCarrier i ∧ y ∈ D.copyCarrier i := by
    fin_cases k
    · constructor
      · simpa [hLabel, hx, OrderOneData.Incident, OrderOneData.carrier]
          using Z.left_incident (0 : Fin 2)
      · simpa [hLabel, hy, cyclicSucc, OrderOneData.Incident,
          OrderOneData.carrier] using Z.right_incident (1 : Fin 2)
    · constructor
      · simpa [hLabel, hx, cyclicSucc, OrderOneData.Incident,
          OrderOneData.carrier] using Z.right_incident (0 : Fin 2)
      · simpa [hLabel, hy, OrderOneData.Incident, OrderOneData.carrier]
          using Z.left_incident (1 : Fin 2)
  obtain ⟨k, hk⟩ := hSome
  have hOwn : b ∈ D.edges (Z.label k) := by
    cases hLabel : Z.label k with
    | inl i =>
        obtain ⟨hix, hiy⟩ := hLabelVertices k i hLabel
        simpa [hLabel, OrderOneData.edges] using
          hStrong i b x y hxy hix hiy hbx hby
    | inr edge =>
        have hFalse : False := by
          simpa [hLabel, OrderOneData.designated] using hk
        exact False.elim hFalse
  exact Z.hasSimultaneousSupreme_of_all_shortValid D hAccept k hk
    (by
      intro j _hNe
      exact ⟨b, hOwn, hBoundary (trainCyclicPred j), hBoundary j⟩)

end StructuralRamsey.Girth.OrderOneData

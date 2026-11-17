import Girth.OrderReductCarrierArrow
import Girth.TrainFillingUniformEdgePresentation
import Mathlib.Data.Finset.Sort

/-! # Ordered representatives of unordered uniform edges -/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v
variable {V : Type v} [Finite V] [LinearOrder V]

/-- Sorting a declared uniform edge gives an ordered induced copy of the
one-edge source, with exactly that unordered carrier. -/
theorem orderedUniformEdgeSupport_exact
    (k : ℕ) (E : Set (Set V))
    (hUniform : ∀ e ∈ E, e.ncard = k) :
    supportCopies (uniformEdgeSource k).ordered (uniformEdgeTarget k E).ordered = E := by
  classical
  apply Set.Subset.antisymm
  · rintro e ⟨f, rfl⟩
    exact uniformEdgeEmbedding_carrier_mem k E f.orderReduct
  · intro e he
    let s := e.toFinite.toFinset
    have hs : s.card = k :=
      (Set.ncard_eq_toFinset_card e e.toFinite).symm.trans (hUniform e he)
    let sorted := s.orderEmbOfFin hs
    have hRange : Set.range (sorted : Fin k → V) = e := by
      exact (Finset.range_orderEmbOfFin s hs).trans e.toFinite.coe_toFinset
    have hEdge : Set.range (sorted : Fin k → V) ∈ E := hRange.symm ▸ he
    let plain := uniformEdgeEmbedding k E sorted.toEmbedding hEdge
    let ordered : Embedding (uniformEdgeSource k).ordered (uniformEdgeTarget k E).ordered :=
      { toFun := plain
        injective := plain.injective
        map_rel_iff := by
          intro r t
          cases r with
          | inl r => exact plain.map_rel_iff r t
          | inr r =>
            change Fin 2 → ULift.{v} (Fin k) at t
            change (sorted (t 0).down < sorted (t 1).down) ↔ (t 0).down < (t 1).down
            exact sorted.strictMono.lt_iff_lt }
    exact ⟨ordered, hRange.symm.trans (uniformEdgeEmbedding_carrier k E _ hEdge).symm⟩

/-- In the fully ordered uniform target, every unordered one-edge image
carrier has an ordered representative. -/
theorem orderedUniformEdge_carrierLift
    (k : ℕ) (E : Set (Set V))
    (hUniform : ∀ e ∈ E, e.ncard = k) :
    supportCopies (uniformEdgeSource k) (uniformEdgeTarget k E) ⊆
      supportCopies (uniformEdgeSource k).ordered (uniformEdgeTarget k E).ordered := by
  rw [orderedUniformEdgeSupport_exact k E hUniform]
  rintro e ⟨f, rfl⟩
  exact uniformEdgeEmbedding_carrier_mem k E f

end StructuralRamsey.Girth

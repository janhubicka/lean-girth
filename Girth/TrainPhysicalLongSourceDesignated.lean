import Girth.TrainOneFreshLongPhysical

/-!
# Physical long geometry forces a genuinely designated SOURCE label

A first-stage PhysicalLongGeometry long piece at original occurrence j
has two vertex boundary connectors x,y and certifies NO ambient
physical edge through both. If the original source occurrence were
labelled by an actual physical edge g, the existing left/right
BigCycle incidence fields would force x,y to lie in g, contrary to
the no-pair clause.

Hence the original label at j must be Sum.inl: a GENUINELY
designated occurrence, not merely an occurrence geometrically owned
by a chosen standard. This is exactly what the target-independent
designated-label count rank needs for a long insertion.

The proof does NOT assume an original designated SUPREME target,
output linearity, an actual replacement, or an owner minimum.
No appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Every genuine physical-only long replacement acts on an
original designated source occurrence. An actual physical edge
source label is impossible by the no-pair-edge condition and its
two original boundary incidences. -/
theorem BigCycle.source_designated_of_physicalLongGeometry
    {n : ℕ} (K : D.BigCycle n)
    (j : Fin n) (first : E) (wagon : P) (second : E)
    (hLong : K.PhysicalLongGeometry D j first wagon second) :
    ∃ i : I, K.label j = Sum.inl i := by
  obtain ⟨x, y, hLeft, hRight, _hNe,
    _hParFirst, _hParSecond, _hFirstX, _hSecondY,
    hNoPair⟩ := hLong
  cases hLabel : K.label j with
  | inl i =>
      exact ⟨i, rfl⟩
  | inr old =>
      exfalso
      have hOldX : x ∈ D.edgeCarrier old := by
        have hInc := K.right_incident (trainCyclicPred j)
        rw [cyclicSucc_trainCyclicPred_of_two_le K.length_ge_two j,
          hLabel, hLeft] at hInc
        exact hInc
      have hOldY : y ∈ D.edgeCarrier old := by
        have hInc := K.left_incident j
        rw [hLabel, hRight] at hInc
        exact hInc
      exact hNoPair ⟨old, hOldX, hOldY⟩

end StructuralRamsey.Girth.OrderOneData

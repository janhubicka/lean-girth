import Girth.TrainBigCycleOrderOneExtraction

/-!
# Circulation: abstract A3 transfer under wagon insertions

A fresh long-piece replacement introduces only wagon connectors. Original
vertex connectors survive in their old cyclic order. Therefore the vertex
contacts of a wagon in the expanded word come from old vertex contacts.

Old A3 confines each nonconnector wagon's vertex contacts to two
consecutive source positions. Such a pair remains consecutive in the
expanded word unless a fresh wagon was inserted between it. Source
wagon linearity and the LongValid geometry forbid precisely this
splitting when BOTH vertices also belong to another nonconnector wagon.

The theorem below isolates that exact transfer. It does not hide the
two real remaining picture-specific obligations:
  (1) every output vertex contact has its original position;
  (2) a pair of old contacts of a nonconnector wagon was not split.

We do not assume the conclusion B.A3, output wagon linearity,
acceptability of B, nor a supreme collapse or appendix theorem.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- If output vertex contacts are precisely inherited from old connector
positions, and no insertion splits the two contacts of a wagon which
is NOT an output connector, then old A3 transfers to output A3.

The proof also handles the important singleton-contact case: if only
one of the two old candidate positions is present, no adjacency
assumption is needed. -/
theorem BigCycle.A3_of_old_contacts_no_split
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (oldPos : Fin n → Fin m)
    (hA3 : C.A3)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (hContactPullback : ∀ (p : P) (j : Fin m),
      B.InWagonAt p j →
      ∃ i : Fin n, j = oldPos i ∧ C.InWagonAt p i)
    (hNoSplit : ∀ (p : P) (i : Fin n),
      (∀ j : Fin m, B.connector j ≠ Sum.inr p) →
      C.InWagonAt p i →
      C.InWagonAt p (cyclicSucc i) →
      oldPos (cyclicSucc i) = cyclicSucc (oldPos i)) :
    B.A3 := by
  intro p hNoOut
  have hNoOld : ∀ i : Fin n, C.connector i ≠ Sum.inr p := by
    intro i hi
    exact hNoOut (oldPos i) (by rw [hConnector i, hi])
  obtain ⟨i, hWindow⟩ := hA3 p hNoOld
  by_cases hi : C.InWagonAt p i
  · by_cases hs : C.InWagonAt p (cyclicSucc i)
    · have hAdjacent := hNoSplit p i hNoOut hi hs
      refine ⟨oldPos i, ?_⟩
      intro j hj
      obtain ⟨t, ht, hContact⟩ := hContactPullback p j hj
      rcases hWindow t hContact with hEq | hEq
      · rw [ht, hEq]
        exact Or.inl rfl
      · rw [ht, hEq, hAdjacent]
        exact Or.inr rfl
    · refine ⟨oldPos i, ?_⟩
      intro j hj
      obtain ⟨t, ht, hContact⟩ := hContactPullback p j hj
      rcases hWindow t hContact with hEq | hEq
      · rw [ht, hEq]
        exact Or.inl rfl
      · exact False.elim (hs (hEq ▸ hContact))
  · refine ⟨oldPos (cyclicSucc i), ?_⟩
    intro j hj
    obtain ⟨t, ht, hContact⟩ := hContactPullback p j hj
    rcases hWindow t hContact with hEq | hEq
    · exact False.elim (hi (hEq ▸ hContact))
    · rw [ht, hEq]
      exact Or.inl rfl

end StructuralRamsey.Girth.OrderOneData

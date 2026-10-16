import Girth.TrainSimultaneousSupreme

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


/-- Source wagon linearity makes the no-splitting hypothesis automatic
whenever a gap between two consecutive original positions is witnessed
by a NEW output wagon containing both original boundary vertices.

The inserted wagon cannot equal an output nonconnector wagon. Hence
if both boundary vertices also lie in that nonconnector wagon, two
distinct source wagons would share two vertices, contradicting
LinearPretrain. This is exactly the geometric observation used in the
circulation admissible-replacement proof. -/
theorem BigCycle.no_split_of_linear_inserted_wagon
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (oldPos : Fin n → Fin m)
    (hLinear : D.LinearPretrain)
    (hInserted : ∀ i : Fin n,
      oldPos (cyclicSucc i) ≠ cyclicSucc (oldPos i) →
      ∃ (q : P) (x y : V),
        C.connector i = Sum.inl x ∧
        C.connector (cyclicSucc i) = Sum.inl y ∧
        D.WagonVertex q x ∧ D.WagonVertex q y ∧
        ∃ j : Fin m, B.connector j = Sum.inr q)
    (p : P) (i : Fin n)
    (hNoOut : ∀ j : Fin m, B.connector j ≠ Sum.inr p)
    (hP : C.InWagonAt p i)
    (hPSucc : C.InWagonAt p (cyclicSucc i)) :
    oldPos (cyclicSucc i) = cyclicSucc (oldPos i) := by
  by_contra hSplit
  obtain ⟨q, x, y, hCx, hCy, hQx, hQy, j, hWagon⟩ :=
    hInserted i hSplit
  obtain ⟨x', hCx', hPx'⟩ := hP
  obtain ⟨y', hCy', hPy'⟩ := hPSucc
  have hXX : x' = x :=
    Sum.inl.inj (hCx'.symm.trans hCx)
  have hYY : y' = y :=
    Sum.inl.inj (hCy'.symm.trans hCy)
  have hPx : D.WagonVertex p x := by
    simpa [hXX] using hPx'
  have hPy : D.WagonVertex p y := by
    simpa [hYY] using hPy'
  have hxy : x ≠ y := by
    intro heq
    have hc : C.connector i = C.connector (cyclicSucc i) := by
      rw [hCx, hCy, heq]
    exact C.adjacent_ne i
      (congrArg C.label (C.connector_injective hc))
  have hpq : p ≠ q := by
    intro heq
    subst q
    exact hNoOut j hWagon
  have hOverlap :
      ({z : V | D.WagonVertex p z} ∩
        {z : V | D.WagonVertex q z}).Subsingleton :=
    hLinear.2 p q hpq
  exact hxy (hOverlap ⟨hPx, hQx⟩ ⟨hPy, hQy⟩)

/-- A3 transfer under an actual connector-position map now needs only
two geometric input facts: output vertex contacts come from source
vertices, and every split of consecutive source positions is caused
by an inserted wagon covering the boundary pair. The latter and
SOURCE wagon linearity derive no-splitting automatically.

This is an interface theorem: constructing the concrete oldPos and
proving these two input facts for resultWord is a separate obligation,
not smuggled into the hypotheses as output A3. -/
theorem BigCycle.A3_of_preserved_contacts_and_insertions
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (oldPos : Fin n → Fin m)
    (hA3 : C.A3) (hLinear : D.LinearPretrain)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (hContactPullback : ∀ (p : P) (j : Fin m),
      B.InWagonAt p j →
      ∃ i : Fin n, j = oldPos i ∧ C.InWagonAt p i)
    (hInserted : ∀ i : Fin n,
      oldPos (cyclicSucc i) ≠ cyclicSucc (oldPos i) →
      ∃ (q : P) (x y : V),
        C.connector i = Sum.inl x ∧
        C.connector (cyclicSucc i) = Sum.inl y ∧
        D.WagonVertex q x ∧ D.WagonVertex q y ∧
        ∃ j : Fin m, B.connector j = Sum.inr q) :
    B.A3 := by
  apply C.A3_of_old_contacts_no_split D B oldPos hA3
    hConnector hContactPullback
  intro p i hNoOut hp hs
  exact C.no_split_of_linear_inserted_wagon D B oldPos
    hLinear hInserted p i hNoOut hp hs

end StructuralRamsey.Girth.OrderOneData

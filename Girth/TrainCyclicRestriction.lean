import Girth.TrainSingleShortReplacement

/-!
# Circulation: cyclic restriction of the actual big-cycle syntax

The retained positions are enumerated by an order embedding between the two
finite cyclic index sets.  Vertex and wagon maps preserve the *actual*
connectors, and the physical wagon-contact and edge hypotheses are stated
separately.  No acceptability condition on the output is a premise.

In particular, an output nonconnector wagon may have been a DELETED source
wagon connector.  Its two possible surviving contacts become consecutive;
this is proved from the position embedding, not assumed as a contact window.
-/

namespace StructuralRamsey.Girth

namespace CyclicRestriction

private theorem value_lt_of_image_lt {m n : ℕ}
    (f : Fin m ↪o Fin n) {i j : Fin m}
    (h : (f i).val < (f j).val) : i.val < j.val := by
  by_contra hij
  have hji : j ≤ i := by exact Nat.le_of_not_gt hij
  have hmap := f.monotone hji
  change (f j).val ≤ (f i).val at hmap
  omega

/-- An empty increasing gap in the retained image is one cyclic step. -/
private theorem successor_of_increasing_gap {m n : ℕ}
    (f : Fin m ↪o Fin n) (i j : Fin m)
    (hij : (f i).val < (f j).val)
    (hgap : ∀ k : Fin m,
      (f i).val < (f k).val → (f k).val < (f j).val → False) :
    j = cyclicSucc i := by
  have hi : i.val < j.val := value_lt_of_image_lt f hij
  have hiLt : i.val + 1 < m := by omega
  have hnext : j.val = i.val + 1 := by
    by_contra hne
    let k : Fin m := ⟨i.val + 1, hiLt⟩
    have hik : i < k := by change i.val < i.val + 1; omega
    have hkj : k < j := by change i.val + 1 < j.val; omega
    exact hgap k (f.strictMono hik) (f.strictMono hkj)
  apply Fin.ext
  change j.val = (i.val + 1) % m
  rw [Nat.mod_eq_of_lt hiLt]
  exact hnext

/-- An empty wrapping gap has the last and first retained positions as ends. -/
private theorem successor_of_wrapping_gap {m n : ℕ}
    (f : Fin m ↪o Fin n) (i j : Fin m)
    (hmax : ∀ k : Fin m, (f i).val < (f k).val → False)
    (hmin : ∀ k : Fin m, (f k).val < (f j).val → False) :
    j = cyclicSucc i := by
  have hiLast : i.val + 1 = m := by
    by_contra hne
    have hiLt : i.val + 1 < m := by omega
    let k : Fin m := ⟨i.val + 1, hiLt⟩
    have hik : i < k := by change i.val < i.val + 1; omega
    exact hmax k (f.strictMono hik)
  have hjZero : j.val = 0 := by
    by_contra hne
    let k : Fin m := ⟨0, by omega⟩
    have hkj : k < j := by change 0 < j.val; omega
    exact hmin k (f.strictMono hkj)
  apply Fin.ext
  change j.val = (i.val + 1) % m
  rw [hiLast, Nat.mod_self, hjZero]

/-- A source successor which survives deletion is the output successor.
The final-to-initial step is included. -/
theorem successor_of_source_successor {m n : ℕ}
    (f : Fin m ↪o Fin n) (i j : Fin m)
    (h : f j = cyclicSucc (f i)) : j = cyclicSucc i := by
  have hv := congrArg Fin.val h
  change (f j).val = ((f i).val + 1) % n at hv
  by_cases hi : (f i).val + 1 < n
  · rw [Nat.mod_eq_of_lt hi] at hv
    apply successor_of_increasing_gap f i j
    · omega
    · intro k hleft hright
      omega
  · have hlast : (f i).val + 1 = n := by omega
    rw [hlast, Nat.mod_self] at hv
    apply successor_of_wrapping_gap f i j
    · intro k hk
      have := (f k).isLt
      omega
    · intro k hk
      omega

/-- The predecessor version of cyclic adjacency reflection. -/
theorem predecessor_of_source_predecessor {m n : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (f : Fin m ↪o Fin n) (i j : Fin m)
    (h : f j = trainCyclicPred (f i)) : j = trainCyclicPred i := by
  have hnext : f i = cyclicSucc (f j) := by
    rw [h, cyclicSucc_trainCyclicPred_of_two_le hn]
  have hji := successor_of_source_successor f j i hnext
  have hp := congrArg trainCyclicPred hji
  rw [trainCyclicPred_cyclicSucc_of_two_le hm] at hp
  exact hp.symm

private theorem predecessor_value_of_positive {n : ℕ} (k : Fin n)
    (hk : 0 < k.val) : (trainCyclicPred k).val = k.val - 1 := by
  change (k.val + n - 1) % n = k.val - 1
  have hsum : k.val + n - 1 = (k.val - 1) + n := by omega
  have hlt : k.val - 1 < n := by omega
  rw [hsum]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]

private theorem predecessor_value_of_zero {n : ℕ} (k : Fin n)
    (hk : k.val = 0) : (trainCyclicPred k).val = n - 1 := by
  change (k.val + n - 1) % n = n - 1
  have hlt : n - 1 < n := by omega
  rw [hk, Nat.zero_add, Nat.mod_eq_of_lt hlt]

/-- If a source position is deleted but both its neighbours survive,
those neighbours are consecutive in the restricted cycle.  Distinctness
of the retained neighbours is explicit, covering the length-two source
exception without an artificial lower bound on the source length. -/
theorem successor_across_deleted_position {m n : ℕ}
    (f : Fin m ↪o Fin n) (i j : Fin m) (k : Fin n)
    (hij : i ≠ j) (hdelete : ∀ a : Fin m, f a ≠ k)
    (hleft : f i = trainCyclicPred k)
    (hright : f j = cyclicSucc k) : j = cyclicSucc i := by
  have hl := congrArg Fin.val hleft
  have hr := congrArg Fin.val hright
  change (f j).val = (k.val + 1) % n at hr
  by_cases hk : k.val = 0
  · rw [predecessor_value_of_zero k hk] at hl
    have hn : 1 < n := by
      have hne : f i ≠ f j := fun h => hij (f.injective h)
      by_contra h
      have hi := (f i).isLt
      have hj := (f j).isLt
      apply hne
      apply Fin.ext
      omega
    rw [hk, Nat.zero_add, Nat.mod_eq_of_lt hn] at hr
    apply successor_of_wrapping_gap f i j
    · intro a ha
      have := (f a).isLt
      omega
    · intro a ha
      apply hdelete a
      apply Fin.ext
      omega
  · have hkPos : 0 < k.val := by omega
    rw [predecessor_value_of_positive k hkPos] at hl
    by_cases hkNext : k.val + 1 < n
    · rw [Nat.mod_eq_of_lt hkNext] at hr
      apply successor_of_increasing_gap f i j
      · omega
      · intro a hia haj
        apply hdelete a
        apply Fin.ext
        omega
    · have hkLast : k.val + 1 = n := by omega
      rw [hkLast, Nat.mod_self] at hr
      apply successor_of_wrapping_gap f i j
      · intro a ha
        apply hdelete a
        apply Fin.ext
        have := (f a).isLt
        omega
      · intro a ha
        omega

/-- Restricting a two-consecutive-position source window leaves a window
of at most two consecutive output positions. -/
theorem restrict_consecutive_window {m n : ℕ}
    (hm : 2 ≤ m) (f : Fin m ↪o Fin n) (k : Fin n)
    (Q : Fin m → Prop)
    (hQ : ∀ j, Q j → f j = k ∨ f j = cyclicSucc k) :
    ∃ i : Fin m, ∀ j, Q j → j = i ∨ j = cyclicSucc i := by
  classical
  by_cases hfirst : ∃ i : Fin m, Q i ∧ f i = k
  · obtain ⟨i, _hi, hfi⟩ := hfirst
    refine ⟨i, ?_⟩
    intro j hj
    rcases hQ j hj with h | h
    · exact Or.inl (f.injective (h.trans hfi.symm))
    · exact Or.inr (successor_of_source_successor f i j (by rw [hfi]; exact h))
  · by_cases hsome : ∃ i : Fin m, Q i
    · obtain ⟨i, hi⟩ := hsome
      have hfi : f i = cyclicSucc k := (hQ i hi).resolve_left
        (fun h => hfirst ⟨i, hi, h⟩)
      refine ⟨i, ?_⟩
      intro j hj
      have hfj : f j = cyclicSucc k := (hQ j hj).resolve_left
        (fun h => hfirst ⟨j, hj, h⟩)
      exact Or.inl (f.injective (hfj.trans hfi.symm))
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro j hj
      exact False.elim (hsome ⟨j, hj⟩)

/-- The source A2 window around a deleted wagon connector becomes an
output A3 window.  Its source predecessor and successor need not be
distinct; in that case the surviving contact set is a singleton. -/
theorem restrict_deleted_neighbour_window {m n : ℕ}
    (hm : 2 ≤ m) (f : Fin m ↪o Fin n) (k : Fin n)
    (hdelete : ∀ a : Fin m, f a ≠ k)
    (Q : Fin m → Prop)
    (hQ : ∀ j, Q j →
      f j = trainCyclicPred k ∨ f j = cyclicSucc k) :
    ∃ i : Fin m, ∀ j, Q j → j = i ∨ j = cyclicSucc i := by
  classical
  by_cases hfirst : ∃ i : Fin m, Q i ∧ f i = trainCyclicPred k
  · obtain ⟨i, _hi, hfi⟩ := hfirst
    refine ⟨i, ?_⟩
    intro j hj
    rcases hQ j hj with h | h
    · exact Or.inl (f.injective (h.trans hfi.symm))
    · by_cases hji : j = i
      · exact Or.inl hji
      · exact Or.inr (successor_across_deleted_position f i j k
          (Ne.symm hji) hdelete hfi h)
  · by_cases hsome : ∃ i : Fin m, Q i
    · obtain ⟨i, hi⟩ := hsome
      have hfi : f i = cyclicSucc k := (hQ i hi).resolve_left
        (fun h => hfirst ⟨i, hi, h⟩)
      refine ⟨i, ?_⟩
      intro j hj
      have hfj : f j = cyclicSucc k := (hQ j hj).resolve_left
        (fun h => hfirst ⟨j, hj, h⟩)
      exact Or.inl (f.injective (hfj.trans hfi.symm))
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro j hj
      exact False.elim (hsome ⟨j, hj⟩)


/-- Deleting cyclic connector positions cannot increase twice-order.
For a retained position whose old successor is also retained the weight
is unchanged.  Otherwise at most one extra unit is charged to that old
successor.  These charged positions are distinct and all are deleted, so
no formal interval partition or list of runs is needed. -/
theorem twiceWeight_restrict_le {m n : ℕ} (hn : 2 ≤ n)
    (f : Fin m ↪o Fin n) (kind : Fin n → CycleConnectorKind) :
    (∑ j : Fin m, twiceOccurrenceWeight (kind (f j))
      (kind (f (cyclicSucc j)))) ≤
    ∑ k : Fin n, twiceOccurrenceWeight (kind k) (kind (cyclicSucc k)) := by
  classical
  let weight : Fin n → ℕ := fun k =>
    twiceOccurrenceWeight (kind k) (kind (cyclicSucc k))
  let retained : Finset (Fin n) := Finset.univ.image f
  let chargedFrom : Finset (Fin m) := Finset.univ.filter
    (fun j => f (cyclicSucc j) ≠ cyclicSucc (f j))
  let charged : Finset (Fin n) := chargedFrom.image (fun j => cyclicSucc (f j))
  have hStep (j : Fin m) :
      twiceOccurrenceWeight (kind (f j)) (kind (f (cyclicSucc j))) ≤
      weight (f j) + if f (cyclicSucc j) ≠ cyclicSucc (f j)
        then weight (cyclicSucc (f j)) else 0 := by
    by_cases h : f (cyclicSucc j) = cyclicSucc (f j)
    · simp [h, weight]
    · rw [if_pos h]
      have hOutput := twiceOccurrenceWeight_le_two
        (kind (f j)) (kind (f (cyclicSucc j)))
      have hFirst := twiceOccurrenceWeight_one_le
        (kind (f j)) (kind (cyclicSucc (f j)))
      have hSecond := twiceOccurrenceWeight_one_le
        (kind (cyclicSucc (f j))) (kind (cyclicSucc (cyclicSucc (f j))))
      change _ ≤ weight (f j) + weight (cyclicSucc (f j))
      dsimp [weight]
      omega
  have hDisjoint : Disjoint retained charged := by
    apply Finset.disjoint_left.mpr
    intro k hkRetained hkCharged
    obtain ⟨i, _hi, hik⟩ := Finset.mem_image.mp hkRetained
    obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hkCharged
    have hNot := (Finset.mem_filter.mp hj).2
    have hSource : f i = cyclicSucc (f j) := hik.trans hjk.symm
    have hOutput := successor_of_source_successor f j i hSource
    apply hNot
    exact (congrArg f hOutput.symm).trans hSource
  have hRetainedSum :
      (∑ j : Fin m, weight (f j)) = ∑ k ∈ retained, weight k := by
    dsimp [retained]
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact f.injective hij
  have hChargedSum :
      (∑ j : Fin m, if f (cyclicSucc j) ≠ cyclicSucc (f j)
        then weight (cyclicSucc (f j)) else 0) =
      ∑ k ∈ charged, weight k := by
    dsimp [charged]
    rw [Finset.sum_image]
    · simp [chargedFrom, Finset.sum_filter]
    · intro i _ j _ hij
      apply f.injective
      have hp := congrArg trainCyclicPred hij
      simpa only [trainCyclicPred_cyclicSucc_of_two_le hn] using hp
  calc
    (∑ j : Fin m, twiceOccurrenceWeight (kind (f j))
        (kind (f (cyclicSucc j)))) ≤
        (∑ j : Fin m, weight (f j)) +
        ∑ j : Fin m, if f (cyclicSucc j) ≠ cyclicSucc (f j)
          then weight (cyclicSucc (f j)) else 0 := by
      simpa only [Finset.sum_add_distrib] using
        (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hStep j))
    _ = ∑ k ∈ retained ∪ charged, weight k := by
      rw [hRetainedSum, hChargedSum, Finset.sum_union hDisjoint]
    _ ≤ ∑ k : Fin n, weight k := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (by intro k _ _; exact Nat.zero_le _)
    _ = _ := rfl

end CyclicRestriction

namespace OrderOneData

universe v w
variable {V E I P : Type v} {V' E' I' P' : Type w}
  {D : OrderOneData V E I P} {D' : OrderOneData V' E' I' P'}

/-- Once adjacent labels and their incidences are checked, inherited
connectors automatically form a legal big cycle.  There is no assumption
that the proposed output connectors are already injective. -/
def BigCycle.restrictConnectorWord {n m : ℕ} (C : D.BigCycle n)
    (hm : 2 ≤ m) (f : Fin m ↪o Fin n)
    (vertex : V' → V) (wagon : P' → P)
    (label : Fin m → I' ⊕ E') (connector : Fin m → V' ⊕ P')
    (hConnector : ∀ j, C.connector (f j) = Sum.map vertex wagon (connector j))
    (hAdjacent : ∀ j, label j ≠ label (cyclicSucc j))
    (hLeft : ∀ j, D'.Incident (label j) (connector j))
    (hRight : ∀ j, D'.Incident (label (cyclicSucc j)) (connector j)) :
    D'.BigCycle m where
  length_ge_two := hm
  label := label
  connector := connector
  adjacent_ne := hAdjacent
  connector_injective := by
    intro i j hij
    apply f.injective
    apply C.connector_injective
    rw [hConnector i, hConnector j, hij]
  left_incident := hLeft
  right_incident := hRight

namespace BigCycle

/-- The geometric hypotheses of the manuscript's cyclic restriction
lemma, between two actual typed big cycles.  The last field asks for
reflection of a common edge ONLY at the two distinct vertex neighbours
of a surviving wagon connector. -/
structure RestrictionMap {n m : ℕ} (C : D.BigCycle n) (B : D'.BigCycle m) where
  position : Fin m ↪o Fin n
  vertex : V' → V
  wagon : P' → P
  vertex_injective : Function.Injective vertex
  wagon_injective : Function.Injective wagon
  connector_eq : ∀ j,
    C.connector (position j) = Sum.map vertex wagon (B.connector j)
  contact : ∀ (p : P') (j : Fin m) (x : V'),
    B.connector j = Sum.inl x → D'.WagonVertex p x →
      D.WagonVertex (wagon p) (vertex x)
  pair_reflect : ∀ (j : Fin m) (p : P') (x y : V'),
    B.connector j = Sum.inr p →
    B.connector (trainCyclicPred j) = Sum.inl x →
    B.connector (cyclicSucc j) = Sum.inl y →
    trainCyclicPred j ≠ cyclicSucc j →
    D'.WagonVertex p x → D'.WagonVertex p y →
    D'.PairEdge x y → D.PairEdge (vertex x) (vertex y)

namespace RestrictionMap

variable {n m : ℕ} {C : D.BigCycle n} {B : D'.BigCycle m}
  (R : C.RestrictionMap B)

/-- Retaining distinct positions cannot increase the cycle length. -/
theorem length_le : m ≤ n := by
  simpa using Fintype.card_le_of_injective R.position R.position.injective

/-- The actual restricted big cycle has no larger order.  Its connector
kind equation is derived from the typed connector map. -/
theorem twiceOrder_le : B.twiceOrder ≤ C.twiceOrder := by
  have hKind (j : Fin m) :
      connectorKind (B.connector j) = connectorKind (C.connector (R.position j)) := by
    rw [R.connector_eq j]
    cases B.connector j <;> rfl
  unfold BigCycle.twiceOrder
  simp only [hKind]
  exact CyclicRestriction.twiceWeight_restrict_le C.length_ge_two
    R.position (fun k => connectorKind (C.connector k))

theorem source_vertex {j : Fin m} {x : V'}
    (h : B.connector j = Sum.inl x) :
    C.connector (R.position j) = Sum.inl (R.vertex x) := by
  rw [R.connector_eq j, h]
  rfl

theorem source_wagon {j : Fin m} {p : P'}
    (h : B.connector j = Sum.inr p) :
    C.connector (R.position j) = Sum.inr (R.wagon p) := by
  rw [R.connector_eq j, h]
  rfl

/-- Wagon contacts are transferred through the actual connector equation
and physical wagon-carrier inclusion. -/
theorem contact_source (p : P') (j : Fin m) (h : B.InWagonAt p j) :
    C.InWagonAt (R.wagon p) (R.position j) := by
  obtain ⟨x, hx, hp⟩ := h
  exact ⟨R.vertex x, R.source_vertex hx, R.contact p j x hx hp⟩

/-- A2 contact positions remain the immediate output neighbours. -/
theorem A2_positions (hA2 : C.A2)
    (i : Fin m) (p : P') (hi : B.connector i = Sum.inr p)
    (j : Fin m) (hj : B.InWagonAt p j) :
    j = trainCyclicPred i ∨ j = cyclicSucc i := by
  rcases hA2.1 (R.position i) (R.wagon p) (R.source_wagon hi)
      (R.position j) (R.contact_source p j hj) with h | h
  · exact Or.inl (CyclicRestriction.predecessor_of_source_predecessor
      B.length_ge_two C.length_ge_two R.position i j h)
  · exact Or.inr (CyclicRestriction.successor_of_source_successor
      R.position i j h)

/-- Both clauses of A2 transfer, including the ambient common-edge
prohibition.  The distinct-side condition is essential: at length two
the two neighbours coincide and that prohibition is vacuous. -/
theorem A2 (hA2 : C.A2) : B.A2 := by
  refine ⟨R.A2_positions hA2, ?_⟩
  intro i p x y hi hx hy hDifferent hpx hpy hPair
  have hSourceX : C.InWagonAt (R.wagon p) (R.position (trainCyclicPred i)) :=
    R.contact_source p _ ⟨x, hx, hpx⟩
  have hSourceY : C.InWagonAt (R.wagon p) (R.position (cyclicSucc i)) :=
    R.contact_source p _ ⟨y, hy, hpy⟩
  have hPred : R.position (trainCyclicPred i) =
      trainCyclicPred (R.position i) := by
    rcases hA2.1 (R.position i) (R.wagon p) (R.source_wagon hi)
        _ hSourceX with h | h
    · exact h
    · exact False.elim (hDifferent
        (CyclicRestriction.successor_of_source_successor R.position
          i (trainCyclicPred i) h))
  have hSucc : R.position (cyclicSucc i) = cyclicSucc (R.position i) := by
    rcases hA2.1 (R.position i) (R.wagon p) (R.source_wagon hi)
        _ hSourceY with h | h
    · have hbad := CyclicRestriction.predecessor_of_source_predecessor
        B.length_ge_two C.length_ge_two R.position i (cyclicSucc i) h
      exact False.elim (hDifferent hbad.symm)
    · exact h
  have hSourceDifferent : trainCyclicPred (R.position i) ≠
      cyclicSucc (R.position i) := by
    intro heq
    apply hDifferent
    apply R.position.injective
    exact hPred.trans (heq.trans hSucc.symm)
  have hxSource : C.connector (trainCyclicPred (R.position i)) =
      Sum.inl (R.vertex x) := by
    rw [← hPred]
    exact R.source_vertex hx
  have hySource : C.connector (cyclicSucc (R.position i)) =
      Sum.inl (R.vertex y) := by
    rw [← hSucc]
    exact R.source_vertex hy
  exact hA2.2 (R.position i) (R.wagon p) (R.vertex x) (R.vertex y)
    (R.source_wagon hi) hxSource hySource hSourceDifferent
    (R.contact p _ x hx hpx) (R.contact p _ y hy hpy)
    (R.pair_reflect i p x y hi hx hy hDifferent hpx hpy hPair)

/-- If a target wagon is absent as a connector, any occurrence of its
image as a source connector must have been deleted.  Wagon injectivity
is used here; source and target wagon types need not coincide. -/
theorem source_wagon_deleted (p : P')
    (hAbsent : ∀ i : Fin m, B.connector i ≠ Sum.inr p)
    (k : Fin n) (hk : C.connector k = Sum.inr (R.wagon p)) :
    ∀ i : Fin m, R.position i ≠ k := by
  intro i hik
  have hMap : Sum.map R.vertex R.wagon (B.connector i) =
      Sum.inr (R.wagon p) := by
    rw [← R.connector_eq i, hik, hk]
  cases hi : B.connector i with
  | inl x => simp [hi] at hMap
  | inr q =>
      have hpq : q = p := R.wagon_injective (by simpa [hi] using hMap)
      exact hAbsent i (by simpa [hpq] using hi)

/-- A3 transfers both when the image wagon is a source nonconnector and
when its unique source wagon-connector position has been deleted. -/
theorem A3 (hA2 : C.A2) (hA3 : C.A3) : B.A3 := by
  classical
  intro p hAbsent
  by_cases hSourceAbsent : ∀ k : Fin n,
      C.connector k ≠ Sum.inr (R.wagon p)
  · obtain ⟨k, hk⟩ := hA3 (R.wagon p) hSourceAbsent
    apply CyclicRestriction.restrict_consecutive_window B.length_ge_two
      R.position k (B.InWagonAt p)
    intro j hj
    exact hk (R.position j) (R.contact_source p j hj)
  · push_neg at hSourceAbsent
    obtain ⟨k, hk⟩ := hSourceAbsent
    apply CyclicRestriction.restrict_deleted_neighbour_window B.length_ge_two
      R.position k (R.source_wagon_deleted p hAbsent k hk) (B.InWagonAt p)
    intro j hj
    exact hA2.1 k (R.wagon p) hk (R.position j) (R.contact_source p j hj)

/-- The manuscript's acceptability conclusion, with the sole remaining
order-one designation obligation shown explicitly.  No designation is
inferred merely from equality of physical carriers. -/
theorem acceptable (hAccept : C.Acceptable)
    (hDesignated : B.twiceOrder = 2 → ∃ i : Fin m, D'.designated (B.label i)) :
    B.Acceptable :=
  ⟨hDesignated, R.A2 hAccept.2.1, R.A3 hAccept.2.1 hAccept.2.2⟩

/-- The length, order, A2 and A3 conclusions of cyclic restriction,
for actual typed source and output big cycles. -/
theorem restrict (hA2 : C.A2) (hA3 : C.A3) :
    m ≤ n ∧ B.twiceOrder ≤ C.twiceOrder ∧ B.A2 ∧ B.A3 :=
  ⟨R.length_le, R.twiceOrder_le, R.A2 hA2, R.A3 hA2 hA3⟩

end RestrictionMap
end BigCycle
end OrderOneData

end StructuralRamsey.Girth

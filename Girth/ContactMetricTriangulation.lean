import Girth.ContactCoveredSide

/-!
# Covered triangulations for arbitrary metric weights

The induction uses an arbitrary cycle predicate that is stable under
increasing restriction.  A real-valued perimeter is such a predicate
whenever its distance has zero diagonal and satisfies the triangle
inequality.  Thus all metrics, and even directed pseudometrics, are
included; the two-sort contact weights play no role in the budget.
-/

namespace StructuralRamsey.Girth

universe v u
variable {V P J : Type v} {K : J → Set (V ⊕ P)}

private theorem contact_distance_prefix_le {X : Type u}
    (d : X → X → ℝ) (hself : ∀ x, d x x = 0)
    (htriangle : ∀ x y z, d x z ≤ d x y + d y z)
    (z : ℕ → X) {a b : ℕ} (hab : a ≤ b) :
    d (z a) (z b) ≤ (∑ k ∈ Finset.range b, d (z k) (z (k + 1))) -
      ∑ k ∈ Finset.range a, d (z k) (z (k + 1)) := by
  induction b, hab using Nat.le_induction with
  | base => simp [hself]
  | succ b hab ih =>
    rw [Finset.sum_range_succ]
    have ht := htriangle (z a) (z b) (z (b + 1))
    linarith

/-- The triangle inequality implies that deleting vertices from a cyclic
sequence, while preserving their cyclic order, cannot increase its
perimeter.  Neither symmetry nor positivity is needed. -/
theorem contact_metric_cyclic_restriction_le {X : Type u}
    (d : X → X → ℝ) (hself : ∀ x, d x x = 0)
    (htriangle : ∀ x y z, d x z ≤ d x y + d y z)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (z : Fin n → X) (f : Fin m ↪o Fin n) :
    (∑ i : Fin m, d (z (f i)) (z (f (cyclicSucc i)))) ≤
      ∑ i : Fin n, d (z i) (z (cyclicSucc i)) := by
  classical
  let zn : ℕ → X := fun k => z ⟨k % n, Nat.mod_lt _ hn⟩
  let p : ℕ → ℝ := fun b => ∑ k ∈ Finset.range b, d (zn k) (zn (k + 1))
  have hz (i : Fin n) : zn i.val = z i := by
    dsimp [zn]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hwrap : zn n = zn 0 := by simp [zn]
  have hpzero : p 0 = 0 := by simp [p]
  have hprefix {a b : ℕ} (hab : a ≤ b) : d (zn a) (zn b) ≤ p b - p a :=
    contact_distance_prefix_le d hself htriangle zn hab
  have htotal : p n = ∑ i : Fin n, d (z i) (z (cyclicSucc i)) := by
    rw [show p n = ∑ i : Fin n, d (zn i.val) (zn (i.val + 1)) from
      Finset.sum_range _]
    apply Finset.sum_congr rfl
    intro i _
    rw [hz]
    rfl
  let last : Fin m := ⟨m - 1, by omega⟩
  have hlocal (i : Fin m) :
      d (z (f i)) (z (f (cyclicSucc i))) ≤
        (if i = last then p n else 0) +
          p (f (cyclicSucc i)).val - p (f i).val := by
    rw [← hz (f i), ← hz (f (cyclicSucc i))]
    by_cases hi : i = last
    · rw [ite_eq_left hi]
      have hleft := hprefix (Nat.le_of_lt (f i).isLt)
      have hright := hprefix (Nat.zero_le (f (cyclicSucc i)).val)
      have ht := htriangle (zn (f i).val) (zn n) (zn (f (cyclicSucc i)).val)
      rw [hwrap] at ht hleft
      rw [hpzero] at hright
      linarith
    · rw [ite_eq_right hi]
      have hnext : i.val + 1 < m := by
        have hv := i.isLt
        have hne : i.val ≠ m - 1 := fun he => hi (Fin.ext he)
        omega
      have hisucc : i < cyclicSucc i := by
        change i.val < (i.val + 1) % m
        rw [Nat.mod_eq_of_lt hnext]
        omega
      have hmap := f.strictMono hisucc
      have hpath := hprefix (Nat.le_of_lt hmap)
      simpa using hpath
  have hperm : (∑ i : Fin m, p (f (cyclicSucc i)).val) =
      ∑ i : Fin m, p (f i).val := by
    have hbij : Function.Bijective (@cyclicSucc m) :=
      ⟨ContactCyclicRestriction.contactCyclicSucc_injective,
        Finite.surjective_of_injective ContactCyclicRestriction.contactCyclicSucc_injective⟩
    exact hbij.sum_comp (fun i => p (f i).val)
  calc
    (∑ i : Fin m, d (z (f i)) (z (f (cyclicSucc i)))) ≤
        ∑ i : Fin m, ((if i = last then p n else 0) +
          p (f (cyclicSucc i)).val - p (f i).val) :=
      Finset.sum_le_sum fun i _ => hlocal i
    _ = p n := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hperm]
      simp
    _ = _ := htotal

namespace ContactPolygon

/-- The perimeter associated to any real-valued distance. -/
def metricWeight (C : ContactPolygon V P) (d : (V ⊕ P) → (V ⊕ P) → ℝ) : ℝ :=
  ∑ i : Fin C.length, d (C.vertex i) (C.vertex (cyclicSucc i))

theorem metricWeight_le_of_increasing {C D : ContactPolygon V P}
    (d : (V ⊕ P) → (V ⊕ P) → ℝ) (hself : ∀ x, d x x = 0)
    (htriangle : ∀ x y z, d x z ≤ d x y + d y z)
    (f : Fin D.length ↪o Fin C.length)
    (hf : ∀ i, D.vertex i = C.vertex (f i)) :
    D.metricWeight d ≤ C.metricWeight d := by
  simp only [metricWeight, hf]
  exact contact_metric_cyclic_restriction_le d hself htriangle
    (by have := D.hlength; omega) (by have := C.hlength; omega) C.vertex f

theorem metricWeight_restrict_le (C : ContactPolygon V P)
    (d : (V ⊕ P) → (V ⊕ P) → ℝ) (hself : ∀ x, d x x = 0)
    (htriangle : ∀ x y z, d x z ≤ d x y + d y z)
    {m : ℕ} (hm : 3 ≤ m) (f : Fin m ↪o Fin C.length) :
    (C.restrict hm f).metricWeight d ≤ C.metricWeight d :=
  metricWeight_le_of_increasing d hself htriangle f (fun _ => rfl)

end ContactPolygon

/-- A cycle budget is stable when it survives an increasing restriction
of the cyclic vertex list. -/
def ContactCycleBudgetStable (Q : ContactPolygon V P → Prop) : Prop :=
  ∀ {C D : ContactPolygon V P} (f : Fin D.length ↪o Fin C.length),
    (∀ i, D.vertex i = C.vertex (f i)) → Q C → Q D

/-- The covered-triangle and chord hypotheses with an arbitrary budget. -/
def ContactBudgetG4 (K : J → Set (V ⊕ P))
    (Q : ContactPolygon V P → Prop) : Prop :=
  ∀ C, C.IsCycle K → Q C →
    (C.length = 3 → C.Covered K) ∧ (4 ≤ C.length → C.HasChord K)

def ContactBudgetSharedChord (K : J → Set (V ⊕ P))
    (Q : ContactPolygon V P → Prop) : Prop :=
  ∀ C, C.IsCycle K → Q C → C.Covered K ∨ C.HasSharedChord K

/-- A recursive covered triangulation. Each cut preserves cyclic order,
covers every original side, and has exactly two common vertices: the
child lengths sum to the parent length plus two, while the split record
already supplies a common chord and covers all parent vertices. -/
inductive ContactCoveredTriangulation (K : J → Set (V ⊕ P)) :
    ContactPolygon V P → Type v where
  | triangle {C : ContactPolygon V P} (htriangle : C.length = 3)
      (hcovered : C.Covered K) : ContactCoveredTriangulation K C
  | split {C : ContactPolygon V P} (S : C.Split K)
      (hleft : StrictMono S.leftMap) (hright : StrictMono S.rightMap)
      (hsize : S.left.length + S.right.length = C.length + 2)
      (left : ContactCoveredTriangulation K S.left)
      (right : ContactCoveredTriangulation K S.right) :
      ContactCoveredTriangulation K C

namespace ContactCoveredTriangulation

/-- The number of covered triangular faces in the recursive dissection. -/
def triangleCount {C : ContactPolygon V P} : ContactCoveredTriangulation K C → ℕ
  | .triangle _ _ => 1
  | .split _ _ _ _ left right => left.triangleCount + right.triangleCount

theorem triangleCount_add_two {C : ContactPolygon V P}
    (T : ContactCoveredTriangulation K C) : T.triangleCount + 2 = C.length := by
  induction T with
  | triangle htriangle _ => simpa [triangleCount] using htriangle.symm
  | split S _ _ hsize _ _ ihleft ihright =>
    simp only [triangleCount]
    omega

/-- Adjacent faces with different covering labels yield a shared chord;
otherwise their common label covers the entire polygon. -/
theorem covered_or_shared_chord {C : ContactPolygon V P}
    (T : ContactCoveredTriangulation K C) : C.Covered K ∨ C.HasSharedChord K := by
  induction T with
  | triangle _ hcovered => exact Or.inl hcovered
  | split S _ _ _ _ _ ihleft ihright => exact S.join_alternatives ihleft ihright

theorem covered_side {C : ContactPolygon V P}
    (T : ContactCoveredTriangulation K C) (k : Fin C.length) :
    C.HasCoveredSide K k := by
  induction T with
  | triangle _ hcovered => exact ContactPolygon.covered_side_of_covered _ hcovered k
  | split S _ _ _ _ _ ihleft ihright =>
    rcases S.side_cover k with ⟨a, ha, ha'⟩ | ⟨a, ha, ha'⟩
    · exact ContactPolygon.covered_side_lift S.leftMap S.left_vertex ha ha' (ihleft a)
    · exact ContactPolygon.covered_side_lift S.rightMap S.right_vertex ha ha' (ihright a)

end ContactCoveredTriangulation

/-- A split-stable budget supports the full covered triangulation
induction, with no fixed contact-weight arithmetic. -/
theorem contactCoveredTriangulation_of_budgetG4
    {Q : ContactPolygon V P → Prop} (hstable : ContactCycleBudgetStable Q)
    (h : ContactBudgetG4 K Q) (C : ContactPolygon V P)
    (hc : C.IsCycle K) (hQ : Q C) : Nonempty (ContactCoveredTriangulation K C) := by
  have aux : ∀ n : ℕ, ∀ C : ContactPolygon V P, C.length = n →
      C.IsCycle K → Q C → Nonempty (ContactCoveredTriangulation K C) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro D hlen hd hbudget
      by_cases htri : D.length = 3
      · exact ⟨.triangle htri ((h D hd hbudget).1 htri)⟩
      · have hfour : 4 ≤ D.length := by have := D.hlength; omega
        obtain ⟨S, hleft, hright, hsize⟩ :=
          D.split_of_chord_monotone hd ((h D hd hbudget).2 hfour)
        have hL : S.left.length < n := S.left_smaller.trans_le (by omega)
        have hR : S.right.length < n := S.right_smaller.trans_le (by omega)
        have hbL : Q S.left := hstable (OrderEmbedding.ofStrictMono S.leftMap hleft)
          S.left_vertex hbudget
        have hbR : Q S.right := hstable (OrderEmbedding.ofStrictMono S.rightMap hright)
          S.right_vertex hbudget
        obtain ⟨TL⟩ := ih S.left.length hL S.left rfl S.left_cycle hbL
        obtain ⟨TR⟩ := ih S.right.length hR S.right rfl S.right_cycle hbR
        exact ⟨.split S hleft hright hsize TL TR⟩
  exact aux C.length C rfl hc hQ

theorem contactBudgetSharedChord_of_G4
    {Q : ContactPolygon V P → Prop} (hstable : ContactCycleBudgetStable Q)
    (h : ContactBudgetG4 K Q) : ContactBudgetSharedChord K Q := by
  intro C hc hQ
  obtain ⟨T⟩ := contactCoveredTriangulation_of_budgetG4 hstable h C hc hQ
  exact T.covered_or_shared_chord

theorem contactBudgetG4_of_sharedChord
    {Q : ContactPolygon V P → Prop} (h : ContactBudgetSharedChord K Q) :
    ContactBudgetG4 K Q := by
  intro C hc hQ
  rcases h C hc hQ with hcover | hshared
  · exact ⟨fun _ => hcover, fun hn => C.covered_hasChord hn hcover⟩
  · exact ⟨fun hn => (C.triangle_not_shared hn hshared).elim,
      fun _ => C.shared_hasChord hshared⟩

theorem contactBudgetSharedChord_iff_G4
    {Q : ContactPolygon V P → Prop} (hstable : ContactCycleBudgetStable Q) :
    ContactBudgetSharedChord K Q ↔ ContactBudgetG4 K Q :=
  ⟨contactBudgetG4_of_sharedChord, contactBudgetSharedChord_of_G4 hstable⟩

theorem contactBudgetCoveredSide_of_G4
    {Q : ContactPolygon V P → Prop} (hstable : ContactCycleBudgetStable Q)
    (h : ContactBudgetG4 K Q) (C : ContactPolygon V P)
    (hc : C.IsCycle K) (hQ : Q C) (k : Fin C.length) : C.HasCoveredSide K k := by
  obtain ⟨T⟩ := contactCoveredTriangulation_of_budgetG4 hstable h C hc hQ
  exact T.covered_side k

/-- Every metric perimeter threshold is a stable cycle budget. -/
theorem contactMetricBudget_stable
    (d : (V ⊕ P) → (V ⊕ P) → ℝ) (hself : ∀ x, d x x = 0)
    (htriangle : ∀ x y z, d x z ≤ d x y + d y z) (q : ℝ) :
    ContactCycleBudgetStable (fun C : ContactPolygon V P => C.metricWeight d ≤ q) := by
  intro C D f hf hC
  exact (ContactPolygon.metricWeight_le_of_increasing d hself htriangle f hf).trans hC

def ContactMetricG4 (K : J → Set (V ⊕ P))
    (d : (V ⊕ P) → (V ⊕ P) → ℝ) (q : ℝ) : Prop :=
  ContactBudgetG4 K (fun C => C.metricWeight d ≤ q)

def ContactMetricSharedChordBound (K : J → Set (V ⊕ P))
    (d : (V ⊕ P) → (V ⊕ P) → ℝ) (q : ℝ) : Prop :=
  ContactBudgetSharedChord K (fun C => C.metricWeight d ≤ q)

/-- The full arbitrary-metric triangulation assertion of
`obs:triangulation`: every cycle within the perimeter bound has a
recursive triangulation by covered triangles. -/
theorem contactCoveredTriangulation_of_metricG4
    {d : (V ⊕ P) → (V ⊕ P) → ℝ} {q : ℝ}
    (hself : ∀ x, d x x = 0) (htriangle : ∀ x y z, d x z ≤ d x y + d y z)
    (h : ContactMetricG4 K d q) (C : ContactPolygon V P)
    (hc : C.IsCycle K) (hw : C.metricWeight d ≤ q) :
    Nonempty (ContactCoveredTriangulation K C) :=
  contactCoveredTriangulation_of_budgetG4 (contactMetricBudget_stable d hself htriangle q)
    h C hc hw

/-- Part (a) for arbitrary metric weights. -/
theorem contactCoveredSide_of_metricG4
    {d : (V ⊕ P) → (V ⊕ P) → ℝ} {q : ℝ}
    (hself : ∀ x, d x x = 0) (htriangle : ∀ x y z, d x z ≤ d x y + d y z)
    (h : ContactMetricG4 K d q) (C : ContactPolygon V P)
    (hc : C.IsCycle K) (hw : C.metricWeight d ≤ q) (k : Fin C.length) :
    C.HasCoveredSide K k :=
  contactBudgetCoveredSide_of_G4 (contactMetricBudget_stable d hself htriangle q)
    h C hc hw k

/-- Part (b) for arbitrary metric weights. -/
theorem contactSharedChordBound_of_metricG4
    {d : (V ⊕ P) → (V ⊕ P) → ℝ} {q : ℝ}
    (hself : ∀ x, d x x = 0) (htriangle : ∀ x y z, d x z ≤ d x y + d y z)
    (h : ContactMetricG4 K d q) : ContactMetricSharedChordBound K d q :=
  contactBudgetSharedChord_of_G4 (contactMetricBudget_stable d hself htriangle q) h

/-- The shared-chord alternative is equivalent to the two hypotheses
in the arbitrary-metric observation. -/
theorem contactSharedChordBound_iff_metricG4
    {d : (V ⊕ P) → (V ⊕ P) → ℝ} {q : ℝ}
    (hself : ∀ x, d x x = 0) (htriangle : ∀ x y z, d x z ≤ d x y + d y z) :
    ContactMetricSharedChordBound K d q ↔ ContactMetricG4 K d q :=
  contactBudgetSharedChord_iff_G4 (contactMetricBudget_stable d hself htriangle q)

end StructuralRamsey.Girth

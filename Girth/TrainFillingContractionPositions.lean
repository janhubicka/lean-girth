import Girth.TrainFillingWagonGeometry
import Girth.TrainFillingMixedNormalization
import Girth.TrainWagonStrongInduced
import Mathlib.Data.Finset.Sort

/-!
# The actual connector positions deleted by filling contraction

Delete exactly a wagon with two distinct neighbouring vertex positions,
both in its carrier, joined by an OLD ambient edge. The incident labels
are derived to be physical edges from mixed normalization, not assumed.
The deleted blocks are disjoint, all vertices survive, and at least two
positions survive. No legal projected cycle is assumed here.
-/

namespace StructuralRamsey.Girth.TrainFilling
universe v
variable {V I P : Type v}
variable (F : TrainFilling V) (copyCarrier : I → Set V)
variable (copyEdges : I → Set F.OldEdge) (parent : F.OldEdge → P)
local notation "O" => F.oldData copyCarrier copyEdges parent
local notation "H" => F.filledData copyCarrier copyEdges parent

/-- The distinct-neighbour condition excludes length-two contraction. -/
def ContractibleBlock {n : ℕ} (C : (H).BigCycle n) (i : Fin n) : Prop :=
  ∃ (p : P) (x y : V),
    C.connector i = Sum.inr p ∧
    C.connector (trainCyclicPred i) = Sum.inl x ∧
    C.connector (cyclicSucc i) = Sum.inl y ∧
    trainCyclicPred i ≠ cyclicSucc i ∧
    (H).WagonVertex p x ∧ (H).WagonVertex p y ∧ (O).PairEdge x y

theorem vertex_not_contractible {n : ℕ} (C : (H).BigCycle n)
    (i : Fin n) (x : V) (hx : C.connector i = Sum.inl x) :
    ¬ F.ContractibleBlock copyCarrier copyEdges parent C i := by
  rintro ⟨p, _u, _z, hp, _⟩
  have hbad : (Sum.inl x : V ⊕ P) = Sum.inr p := hx.symm.trans hp
  cases hbad

theorem contractible_neighbours_retained {n : ℕ} (C : (H).BigCycle n)
    (i : Fin n) (hi : F.ContractibleBlock copyCarrier copyEdges parent C i) :
    ¬ F.ContractibleBlock copyCarrier copyEdges parent C (trainCyclicPred i) ∧
    ¬ F.ContractibleBlock copyCarrier copyEdges parent C (cyclicSucc i) := by
  obtain ⟨p, x, y, _hp, hx, hy, _⟩ := hi
  exact ⟨F.vertex_not_contractible copyCarrier copyEdges parent C _ x hx,
    F.vertex_not_contractible copyCarrier copyEdges parent C _ y hy⟩

theorem contractionBlocks_disjoint {n : ℕ} (C : (H).BigCycle n)
    (i j : Fin n)
    (hi : F.ContractibleBlock copyCarrier copyEdges parent C i)
    (hj : F.ContractibleBlock copyCarrier copyEdges parent C j)
    (hij : i ≠ j) :
    ∀ k : Fin n, (k = i ∨ k = cyclicSucc i) →
      (k = j ∨ k = cyclicSucc j) → False := by
  intro k hki hkj
  have hni := (F.contractible_neighbours_retained copyCarrier copyEdges parent C i hi).2
  have hnj := (F.contractible_neighbours_retained copyCarrier copyEdges parent C j hj).2
  rcases hki with hki | hki <;> rcases hkj with hkj | hkj
  · exact hij (hki.symm.trans hkj)
  · apply hnj
    have heq : cyclicSucc j = i := hkj.symm.trans hki
    rw [heq]
    exact hi
  · apply hni
    have heq : cyclicSucc i = j := hki.symm.trans hkj
    rw [heq]
    exact hj
  · apply hij
    have heq : cyclicSucc i = cyclicSucc j := hki.symm.trans hkj
    have hpred := congrArg trainCyclicPred heq
    simpa only [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two] using hpred

/-- Normalization makes both incident labels physical edges. -/
theorem contractible_has_edge_occurrences {n : ℕ} (C : (H).BigCycle n)
    (hNormal : C.MixedNormalized H) (i : Fin n)
    (hi : F.ContractibleBlock copyCarrier copyEdges parent C i) :
    ∃ a b : F.NewEdge,
      C.label i = Sum.inr a ∧ C.label (cyclicSucc i) = Sum.inr b ∧ a ≠ b := by
  obtain ⟨p, x, y, hp, hx, hy, _hDifferent, hpx, hpy, _hPair⟩ := hi
  have hLeftMixed : C.MixedWagonContact H i :=
    ⟨x, p, hpx, Or.inl ⟨hx, hp⟩⟩
  have hRightMixed : C.MixedWagonContact H (cyclicSucc i) := by
    refine ⟨y, p, hpy, Or.inr ⟨?_, hy⟩⟩
    rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i]
    exact hp
  have hNotLeft : ¬ (H).designated (C.label i) := by
    intro h
    exact hNormal i h hLeftMixed
  have hNotRight : ¬ (H).designated (C.label (cyclicSucc i)) := by
    intro h
    exact hNormal (cyclicSucc i) h hRightMixed
  cases ha : C.label i with
  | inl a =>
      exact False.elim (hNotLeft (by rw [ha]; trivial))
  | inr a =>
      cases hb : C.label (cyclicSucc i) with
      | inl b =>
          exact False.elim (hNotRight (by rw [hb]; trivial))
      | inr b =>
          refine ⟨a, b, rfl, rfl, ?_⟩
          intro hab
          exact C.adjacent_ne i (ha.trans ((congrArg Sum.inr hab).trans hb.symm))

/-- The old joining edge is unique and belongs to this same wagon. -/
theorem contractible_unique_old_edge {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (i : Fin n)
    (hi : F.ContractibleBlock copyCarrier copyEdges parent C i) :
    ∃ (p : P) (x y : V) (f : F.OldEdge),
      C.connector i = Sum.inr p ∧
      C.connector (trainCyclicPred i) = Sum.inl x ∧
      C.connector (cyclicSucc i) = Sum.inl y ∧
      x ≠ y ∧ x ∈ f.1 ∧ y ∈ f.1 ∧ parent f = p ∧
      ∀ g : F.OldEdge, x ∈ g.1 → y ∈ g.1 → g = f := by
  obtain ⟨p, x, y, hp, hx, hy, hDifferent, hpx, hpy, f, hxf, hyf⟩ := hi
  have hxy : x ≠ y := by
    intro h
    apply hDifferent
    apply C.connector_injective
    exact hx.trans ((congrArg Sum.inl h).trans hy.symm)
  have hxOld := (F.wagonVertex_filled_iff_old copyCarrier copyEdges parent p x).mp hpx
  have hyOld := (F.wagonVertex_filled_iff_old copyCarrier copyEdges parent p y).mp hpy
  have hParent := (O).parent_eq_of_two_vertices_in_wagon hOld
    f p x y hxf hyf hxOld hyOld hxy
  refine ⟨p, x, y, f, hp, hx, hy, hxy, hxf, hyf, hParent, ?_⟩
  intro g hxg hyg
  by_contra hgf
  exact hxy (hOld.1 g f hgf ⟨hxg, hxf⟩ ⟨hyg, hyf⟩)

theorem exists_two_retained {n : ℕ} (C : (H).BigCycle n) :
    ∃ a b : Fin n, a ≠ b ∧
      ¬ F.ContractibleBlock copyCarrier copyEdges parent C a ∧
      ¬ F.ContractibleBlock copyCarrier copyEdges parent C b := by
  classical
  by_cases hSome : ∃ i, F.ContractibleBlock copyCarrier copyEdges parent C i
  · obtain ⟨i, hi⟩ := hSome
    have hNeighbours := F.contractible_neighbours_retained copyCarrier copyEdges parent C i hi
    obtain ⟨_p, _x, _y, _hp, _hx, _hy, hDifferent, _⟩ := hi
    exact ⟨trainCyclicPred i, cyclicSucc i, hDifferent, hNeighbours⟩
  · have hn := C.length_ge_two
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    refine ⟨a, b, ?_, ?_, ?_⟩
    · intro h
      have hv := congrArg Fin.val h
      change 0 = 1 at hv
      omega
    · intro h
      exact hSome ⟨a, h⟩
    · intro h
      exact hSome ⟨b, h⟩

noncomputable def retainedPositions {n : ℕ} (C : (H).BigCycle n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ¬ F.ContractibleBlock copyCarrier copyEdges parent C i)

theorem retainedPositions_mem_iff {n : ℕ} (C : (H).BigCycle n) (i : Fin n) :
    i ∈ F.retainedPositions copyCarrier copyEdges parent C ↔
      ¬ F.ContractibleBlock copyCarrier copyEdges parent C i := by
  classical
  simp [retainedPositions]

theorem retainedPositions_card_two_le {n : ℕ} (C : (H).BigCycle n) :
    2 ≤ (F.retainedPositions copyCarrier copyEdges parent C).card := by
  classical
  obtain ⟨a, b, hab, ha, hb⟩ := F.exists_two_retained copyCarrier copyEdges parent C
  have hsub : ({a, b} : Finset (Fin n)) ⊆
      F.retainedPositions copyCarrier copyEdges parent C := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with hk | hk
    · rw [hk]
      exact (F.retainedPositions_mem_iff copyCarrier copyEdges parent C a).mpr ha
    · rw [hk]
      exact (F.retainedPositions_mem_iff copyCarrier copyEdges parent C b).mpr hb
  have hc := Finset.card_le_card hsub
  simpa [hab] using hc

noncomputable def retainedIndex {n : ℕ} (C : (H).BigCycle n) :
    Fin (F.retainedPositions copyCarrier copyEdges parent C).card ↪o Fin n :=
  (F.retainedPositions copyCarrier copyEdges parent C).orderEmbOfFin rfl

theorem retainedIndex_image {n : ℕ} (C : (H).BigCycle n) :
    Finset.image (F.retainedIndex copyCarrier copyEdges parent C) Finset.univ =
      F.retainedPositions copyCarrier copyEdges parent C := by
  classical
  unfold retainedIndex
  exact Finset.image_orderEmbOfFin_univ
    (F.retainedPositions copyCarrier copyEdges parent C) rfl

theorem retainedIndex_not_contractible {n : ℕ} (C : (H).BigCycle n)
    (j : Fin (F.retainedPositions copyCarrier copyEdges parent C).card) :
    ¬ F.ContractibleBlock copyCarrier copyEdges parent C
      (F.retainedIndex copyCarrier copyEdges parent C j) := by
  classical
  apply (F.retainedPositions_mem_iff copyCarrier copyEdges parent C _).mp
  have hMem : F.retainedIndex copyCarrier copyEdges parent C j ∈
      Finset.image (F.retainedIndex copyCarrier copyEdges parent C) Finset.univ :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  exact (congrArg (fun s : Finset (Fin n) =>
    F.retainedIndex copyCarrier copyEdges parent C j ∈ s)
    (F.retainedIndex_image copyCarrier copyEdges parent C)).mp hMem
end StructuralRamsey.Girth.TrainFilling

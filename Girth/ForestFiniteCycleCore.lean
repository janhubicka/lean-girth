import Girth.Berge
import Mathlib.Tactic

/-!
# Finite ambient witnesses for all short-cycle tests of a batch of edges

Fix any (possibly infinite) old support H and a finite batch K of candidate
support edges. For each subfamily J ⊆ K with a short Berge cycle in H ∪ J,
choose one such cycle, and retain only its old edges. Taking the union of
these old witnesses gives a finite core F ⊆ H of at most g * 2^|K| edges.

For every subfamily J ⊆ K, the augmented supports H ∪ J and F ∪ J have
exactly the same girth-g outcome. In particular, the theorem handles an
entire finite B-copy attachment and every partial sequence of its edges,
not just one fresh edge. No marked-boundary or linearity hypothesis is
needed. This is a static finite witness reduction, NOT a uniform
successor-history representation or a B-carrier forest theorem.
-/

namespace StructuralRamsey.Girth

universe v

/-- Select only the old edges in one bounded cycle witness, if the
candidate attachment actually has such a cycle. -/
noncomputable def oldShortCycleWitnessEdges {W : Type v}
    (H : Set (Set W)) (J : Finset (Set W)) (g : ℕ) :
    Finset (Set W) := by
  classical
  exact if h : HasBergeCycleAtMost (H ∪ (↑J : Set (Set W))) g then
    ((Finset.univ : Finset (Fin (Classical.choose h).length)).image
      (Classical.choose h).edge).filter (fun e => e ∈ H)
  else ∅

/-- A chosen witness contains only old ambient edges. -/
theorem oldShortCycleWitnessEdges_subset {W : Type v}
    (H : Set (Set W)) (J : Finset (Set W)) (g : ℕ) :
    (↑(oldShortCycleWitnessEdges H J g) : Set (Set W)) ⊆ H := by
  classical
  intro e he
  change e ∈ oldShortCycleWitnessEdges H J g at he
  unfold oldShortCycleWitnessEdges at he
  split_ifs at he with h
  · exact (Finset.mem_filter.mp he).2
  · simpa using he

/-- Every selected cycle witness has at most g old edges. -/
theorem oldShortCycleWitnessEdges_card_le {W : Type v}
    (H : Set (Set W)) (J : Finset (Set W)) (g : ℕ) :
    (oldShortCycleWitnessEdges H J g).card ≤ g := by
  classical
  unfold oldShortCycleWitnessEdges
  split_ifs with h
  · calc
      (((Finset.univ : Finset (Fin (Classical.choose h).length)).image
          (Classical.choose h).edge).filter (fun e => e ∈ H)).card ≤
        ((Finset.univ : Finset (Fin (Classical.choose h).length)).image
          (Classical.choose h).edge).card :=
        Finset.card_filter_le _ _
      _ ≤ (Finset.univ : Finset (Fin (Classical.choose h).length)).card :=
        Finset.card_image_le
      _ = (Classical.choose h).length := by simp
      _ ≤ g := Classical.choose_spec h
  · simp

/-- If the enlarged support has a short cycle, one such cycle lies
entirely inside the chosen old witness together with the proposed edges. -/
theorem oldShortCycleWitnessEdges_covers {W : Type v}
    (H : Set (Set W)) (J : Finset (Set W)) (g : ℕ)
    (h : HasBergeCycleAtMost (H ∪ (↑J : Set (Set W))) g) :
    ∃ c : BergeCycle (H ∪ (↑J : Set (Set W))),
      c.length ≤ g ∧ ∀ i,
        c.edge i ∈
          (↑(oldShortCycleWitnessEdges H J g) : Set (Set W)) ∪
            (↑J : Set (Set W)) := by
  classical
  let c : BergeCycle (H ∪ (↑J : Set (Set W))) := Classical.choose h
  refine ⟨c, Classical.choose_spec h, ?_⟩
  intro i
  by_cases hOld : c.edge i ∈ H
  · left
    change c.edge i ∈ oldShortCycleWitnessEdges H J g
    unfold oldShortCycleWitnessEdges
    rw [dif_pos h]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hOld⟩
  · right
    exact (c.edge_mem i).resolve_left hOld

/-- Keep one old cycle witness for every subfamily of the candidate batch.
The candidate edges themselves are not included in the core. -/
noncomputable def finiteBatchCycleCore {W : Type v}
    (H : Set (Set W)) (K : Finset (Set W)) (g : ℕ) :
    Finset (Set W) := by
  classical
  exact K.powerset.biUnion (fun J => oldShortCycleWitnessEdges H J g)

/-- Every edge of the finite cycle core comes from the old support. -/
theorem finiteBatchCycleCore_subset {W : Type v}
    (H : Set (Set W)) (K : Finset (Set W)) (g : ℕ) :
    (↑(finiteBatchCycleCore H K g) : Set (Set W)) ⊆ H := by
  classical
  intro e he
  change e ∈ finiteBatchCycleCore H K g at he
  unfold finiteBatchCycleCore at he
  obtain ⟨J, _, heJ⟩ := Finset.mem_biUnion.mp he
  exact oldShortCycleWitnessEdges_subset H J g heJ

/-- A uniform bound, independent of the size of the old host. -/
theorem finiteBatchCycleCore_card_le {W : Type v}
    (H : Set (Set W)) (K : Finset (Set W)) (g : ℕ) :
    (finiteBatchCycleCore H K g).card ≤ g * 2 ^ K.card := by
  classical
  calc
    (finiteBatchCycleCore H K g).card ≤
        ∑ J ∈ K.powerset, (oldShortCycleWitnessEdges H J g).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _J ∈ K.powerset, g := by
      apply Finset.sum_le_sum
      intro J _
      exact oldShortCycleWitnessEdges_card_le H J g
    _ = g * 2 ^ K.card := by
      simp [Finset.card_powerset, mul_comm]

/-- All subsets of a finite batch have exactly the same short-cycle
outcome over the original host and over the finite core. The same
finite core works simultaneously for every subset J ⊆ K. -/
theorem finiteBatchCycleCore_girth_iff {W : Type v}
    (H : Set (Set W)) (K J : Finset (Set W)) (g : ℕ)
    (hJ : J ⊆ K) :
    GirthGT (H ∪ (↑J : Set (Set W))) g ↔
      GirthGT
        ((↑(finiteBatchCycleCore H K g) : Set (Set W)) ∪
          (↑J : Set (Set W))) g := by
  classical
  have hCoreSub := finiteBatchCycleCore_subset H K g
  constructor
  · intro hGirth
    apply girthGT_of_subset
      (H := (↑(finiteBatchCycleCore H K g) : Set (Set W)) ∪
        (↑J : Set (Set W))) (K := H ∪ (↑J : Set (Set W)))
    · intro e he
      rcases he with heCore | heJ
      · exact Or.inl (hCoreSub heCore)
      · exact Or.inr heJ
    · exact hGirth
  · intro hGirth hBad
    have hIn : J ∈ K.powerset := Finset.mem_powerset.mpr hJ
    obtain ⟨c, hc, hEdges⟩ :=
      oldShortCycleWitnessEdges_covers H J g hBad
    have hOldToCore :
        (↑(oldShortCycleWitnessEdges H J g) : Set (Set W)) ⊆
          (↑(finiteBatchCycleCore H K g) : Set (Set W)) := by
      intro e he
      change e ∈ finiteBatchCycleCore H K g
      unfold finiteBatchCycleCore
      apply Finset.mem_biUnion.mpr
      exact ⟨J, hIn, he⟩
    have hNewEdges (i : Fin c.length) :
        c.edge i ∈
          (↑(finiteBatchCycleCore H K g) : Set (Set W)) ∪
            (↑J : Set (Set W)) := by
      rcases hEdges i with heOld | heJ
      · exact Or.inl (hOldToCore heOld)
      · exact Or.inr heJ
    exact hGirth ⟨c.ofEdgeMem hNewEdges, hc⟩

end StructuralRamsey.Girth

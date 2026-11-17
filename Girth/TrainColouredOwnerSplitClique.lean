import Girth.TrainColouredEdgeOwnerSplit

set_option autoImplicit false

namespace StructuralRamsey.Girth.ColouredEdgeOwnerSplit

universe v
variable {V I : Type v} (H : ColouredEdgeOwnerSplit V I)

/-- Splitting forbidden-predicate vertices by their actual incident edge
preserves coverage of every nonsingleton clique of the pair shadow by an
edge. A clique containing a forbidden vertex is in that vertex's only
incident edge. In the all-allowed case, the original clique suffices. -/
theorem clique_subset_splitEdge
    (hOld : ∀ S : Set V,
      (∃ x ∈ S, ∃ y ∈ S, x ≠ y) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ e : H.OldEdge, x ∈ e.1 ∧ y ∈ e.1) →
      ∃ e : H.OldEdge, S ⊆ e.1)
    (S : Set H.Vertex)
    (hPair : ∃ z ∈ S, ∃ w ∈ S, z ≠ w)
    (hPairs : ∀ z ∈ S, ∀ w ∈ S, z ≠ w →
      ∃ e : H.OldEdge, z ∈ H.splitEdge e ∧ w ∈ H.splitEdge e) :
    ∃ e : H.OldEdge, S ⊆ H.splitEdge e := by
  classical
  obtain ⟨z₀, hz₀, z₁, hz₁, h01⟩ := hPair
  have hCovered (z : H.Vertex) (hz : z ∈ S) :
      ∃ e : H.OldEdge, z ∈ H.splitEdge e := by
    by_cases h : z = z₀
    · obtain ⟨e, he, _⟩ := hPairs z hz z₁ hz₁ (fun hEq => h01 (h.symm.trans hEq))
      exact ⟨e, he⟩
    · obtain ⟨e, he, _⟩ := hPairs z hz z₀ hz₀ h
      exact ⟨e, he⟩
  by_cases hForbidden : ∃ z ∈ S, H.newPredicate z ∉ H.allowed
  · obtain ⟨z, hz, hForbidden⟩ := hForbidden
    obtain ⟨e, he⟩ := hCovered z hz
    refine ⟨e, ?_⟩
    intro w hw
    by_cases h : z = w
    · exact h ▸ he
    · obtain ⟨f, hf, hwf⟩ := hPairs z hz w hw h
      have hef : e = f := by
        by_contra hne
        obtain ⟨x, hx, hzx⟩ := H.intersection_only_allowed e f hne z he hf
        exact hForbidden (by simpa [hzx, newPredicate, project] using hx)
      exact hef.symm ▸ hwf
  · have hInjective : Set.InjOn H.project S := by
      intro z hz w hw hzw
      by_contra hne
      obtain ⟨e, ⟨x, _, rfl⟩, ⟨y, _, rfl⟩⟩ := hPairs z hz w hw hne
      have hxy : x = y := by simpa only [project_place] using hzw
      exact hne (congrArg (H.place e) hxy)
    have hOldPair : ∃ x ∈ H.project '' S, ∃ y ∈ H.project '' S, x ≠ y :=
      ⟨H.project z₀, ⟨z₀, hz₀, rfl⟩, H.project z₁, ⟨z₁, hz₁, rfl⟩,
        fun h => h01 (hInjective hz₀ hz₁ h)⟩
    have hOldPairs (x : V) (hx : x ∈ H.project '' S)
        (y : V) (hy : y ∈ H.project '' S) (hne : x ≠ y) :
        ∃ e : H.OldEdge, x ∈ e.1 ∧ y ∈ e.1 := by
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨w, hw, rfl⟩ := hy
      obtain ⟨e, he, hf⟩ := hPairs z hz w hw (fun h => hne (congrArg H.project h))
      refine ⟨e, ?_, ?_⟩
      · rw [← H.projection_splitEdge e]
        exact ⟨z, he, rfl⟩
      · rw [← H.projection_splitEdge e]
        exact ⟨w, hf, rfl⟩
    obtain ⟨e, he⟩ := hOld (H.project '' S) hOldPair hOldPairs
    refine ⟨e, ?_⟩
    intro z hz
    obtain ⟨f, ⟨x, _, rfl⟩⟩ := hCovered z hz
    have hAllow : H.predicate x ∈ H.allowed := by
      by_contra hn
      exact hForbidden ⟨H.place f x, hz, by simpa only [newPredicate_place] using hn⟩
    have hx : x ∈ e.1 := he ⟨H.place f x, hz, H.project_place f x⟩
    exact ⟨x, hx, by simp [place, hAllow]⟩

end StructuralRamsey.Girth.ColouredEdgeOwnerSplit

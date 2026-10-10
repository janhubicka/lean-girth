import Girth.ForestDistinctBoundaryAllCore

/-!
# Canonical physical boundary port data for finite selected families

The large boundaries are the DISTINCT members of the finite image of
i ↦ carrier(selected i) ∩ S that are not subsingletons. Thus one
physical edge is represented by exactly one label, and there are
at most as many labels as selected members.

A port is chosen for every member from its actual boundary:
- empty -> no port,
- singleton -> the canonical local vertex,
- nonsubsingleton -> the entire physical large boundary.

No Ramsey property is used. This is the final data bridge toward the
all-distinct branch of the direct forest increment.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- Distinct non-subsingleton intersections with the local core. -/
noncomputable def usedWholeBoundaries [Fintype I]
    (selected : I → HypergraphPiece W) (S : Set W) :
    Finset (Set W) := by
  classical
  exact
    (Finset.univ.image (fun i : I => (selected i).carrier ∩ S)).filter
      (fun e => ¬ e.Subsingleton)

/-- Physical edges are indexed by their actual vertex sets, not by
the selected members using them. Duplicates are impossible. -/
abbrev UsedWholeBoundaryEdge [Fintype I]
    (selected : I → HypergraphPiece W) (S : Set W) :=
  {e : Set W // e ∈ usedWholeBoundaries selected S}

/-- There are at most as many distinct large boundaries as members. -/
theorem usedWholeBoundary_card_le [Fintype I]
    (selected : I → HypergraphPiece W) (S : Set W) :
    Fintype.card (UsedWholeBoundaryEdge selected S) ≤
      Fintype.card I := by
  classical
  calc
    Fintype.card (UsedWholeBoundaryEdge selected S) =
        (usedWholeBoundaries selected S).card := by
          exact Fintype.card_coe _
    _ ≤ (Finset.univ.image
        (fun i : I => (selected i).carrier ∩ S)).card := by
          exact Finset.card_filter_le _ _
    _ ≤ Fintype.card I := by
          simpa using
            (Finset.card_image_le :
              (Finset.univ.image
                (fun i : I => (selected i).carrier ∩ S)).card ≤
              (Finset.univ : Finset I).card)

/-- Every represented physical boundary edge is a true local support
edge as soon as the original boundaries are small or whole edges. -/
theorem usedWholeBoundary_mem_local
    [Fintype I]
    (selected : I → HypergraphPiece W)
    (S : Set W) (K : Set (Set W))
    (hBoundary : ∀ i, SmallOrWholeEdgeBoundary K S (selected i))
    (e : UsedWholeBoundaryEdge selected S) :
    (e : Set W) ∈ K := by
  classical
  have he :
      (e : Set W) ∈
        (Finset.univ.image
          (fun i : I => (selected i).carrier ∩ S)).filter
          (fun f => ¬ f.Subsingleton) := by
    simpa [usedWholeBoundaries] using e.property
  obtain ⟨hImage, hLarge⟩ := Finset.mem_filter.mp he
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hImage
  have hNotSmall :
      ¬((selected i).carrier ∩ S).Subsingleton := by
    intro hSmall
    rw [hi] at hSmall
    exact hLarge hSmall
  obtain ⟨f, hfK, _hfSupp, hfBoundary⟩ :=
    (hBoundary i).resolve_left hNotSmall
  have hEq : f = (e : Set W) := hfBoundary.symm.trans hi
  exact hEq ▸ hfK

/-- Every used physical boundary edge lies inside the local core. -/
theorem usedWholeBoundary_subset_core
    [Fintype I]
    (selected : I → HypergraphPiece W)
    (S : Set W)
    (e : UsedWholeBoundaryEdge selected S) :
    (e : Set W) ⊆ S := by
  classical
  have he :
      (e : Set W) ∈
        (Finset.univ.image
          (fun i : I => (selected i).carrier ∩ S)).filter
          (fun f => ¬ f.Subsingleton) := by
    simpa [usedWholeBoundaries] using e.property
  obtain ⟨hImage, _⟩ := Finset.mem_filter.mp he
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hImage
  rw [← hi]
  exact Set.inter_subset_right

/-- The canonical physical edge indices and ALL local vertices admit
exact ports for every selected member, including empty boundaries. -/
theorem exists_canonicalBoundaryPorts
    [Fintype I]
    (selected : I → HypergraphPiece W)
    (S : Set W) :
    ∃ port : I → Option (UsedWholeBoundaryEdge selected S ⊕ S),
      BoundaryPortExact selected S
        (fun e : UsedWholeBoundaryEdge selected S => (e : Set W))
        (fun v : S => (v : W)) port := by
  classical
  have hOne (i : I) :
      ∃ port : Option (UsedWholeBoundaryEdge selected S ⊕ S),
        match port with
        | none => (selected i).carrier ∩ S = ∅
        | some (.inl e) => (selected i).carrier ∩ S = (e : Set W)
        | some (.inr v) => (selected i).carrier ∩ S = {(v : W)} := by
    let b : Set W := (selected i).carrier ∩ S
    by_cases hSmall : b.Subsingleton
    · by_cases hEmpty : b = ∅
      · exact ⟨none, hEmpty⟩
      · obtain ⟨x, hx⟩ : b.Nonempty :=
          Set.nonempty_iff_ne_empty.mpr hEmpty
        have hEq : b = {x} := by
          apply Set.Subset.antisymm
          · intro y hy
            exact Set.mem_singleton_iff.mpr (hSmall hy hx)
          · intro y hy
            have hyx : y = x := by simpa using hy
            subst y
            exact hx
        exact ⟨some (.inr (⟨x, hx.2⟩ : S)), hEq⟩
    · have hMem : b ∈ usedWholeBoundaries selected S := by
        classical
        simp only [usedWholeBoundaries, Finset.mem_filter,
          Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨i, rfl⟩, hSmall⟩
      exact ⟨some (.inl (⟨b, hMem⟩ :
        UsedWholeBoundaryEdge selected S)), rfl⟩
  choose port hPort using hOne
  refine ⟨port, ?_⟩
  intro i
  cases hp : port i with
  | none =>
      simpa [BoundaryPortExact, hp] using hPort i
  | some z =>
      cases z with
      | inl e =>
          simpa [BoundaryPortExact, hp] using hPort i
      | inr v =>
          simpa [BoundaryPortExact, hp] using hPort i

end StructuralRamsey.Girth

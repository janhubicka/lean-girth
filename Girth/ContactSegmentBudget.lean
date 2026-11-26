import Girth.ContactBoundary

/-! Counting segments in the bottom-cut case. When no segment
consists of a single mixed side, charge two distinct units of
original polygon weight to every segment. -/

namespace StructuralRamsey.Girth
universe v
variable {U R O : Type v}

namespace ContactRunSegments
variable {B : ContactPolygon U R} {K : O → Set (U ⊕ R)}
    (S : ContactRunSegments B.vertex K)

theorem next_boundary_eq (i j : Fin S.count)
    (h : S.boundary j = cyclicSucc (S.boundary i)) : j = cyclicSucc i :=
  ContactCyclicRestriction.successor_of_source_successor S.boundary i j h

/-- Each segment starts at its own boundary. If the first side is
mixed, the following point is not a boundary, so charge its outgoing
side as well. The charged positions are distinct and disjoint from
the boundary set. -/
theorem count_twice_le_weight
    (hn : ∀ i : Fin S.count,
      S.boundary (cyclicSucc i) = cyclicSucc (S.boundary i) →
      2 ≤ contactWeight (B.vertex (S.boundary i))
        (B.vertex (cyclicSucc (S.boundary i)))) :
    2 * S.count ≤ B.twiceWeight := by
  classical
  let wt : Fin B.length → ℕ := fun k =>
    contactWeight (B.vertex k) (B.vertex (cyclicSucc k))
  let cut : Finset (Fin B.length) := Finset.univ.image S.boundary
  let light : Finset (Fin S.count) :=
    Finset.univ.filter (fun i => wt (S.boundary i) < 2)
  let charge : Finset (Fin B.length) :=
    light.image (fun i => cyclicSucc (S.boundary i))
  have hd : Disjoint cut charge := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hk
    obtain ⟨i,hi,hi'⟩ := Finset.mem_image.mp hk'
    have he := S.next_boundary_eq i j (hj.trans hi'.symm)
    have hnext : S.boundary (cyclicSucc i) = cyclicSucc (S.boundary i) := by
      rw [← he,hj,← hi']
    exact (Nat.not_lt_of_ge (hn i hnext)) (Finset.mem_filter.mp hi).2
  have hbound : ∀ i : Fin S.count,
      2 ≤ wt (S.boundary i) +
        if wt (S.boundary i) < 2 then wt (cyclicSucc (S.boundary i)) else 0 := by
    intro i
    have hpos : 1 ≤ wt (S.boundary i) := contactWeight_positive _ _
    have hpos' : 1 ≤ wt (cyclicSucc (S.boundary i)) := contactWeight_positive _ _
    split_ifs <;> omega
  have hcut : (∑ i : Fin S.count, wt (S.boundary i)) = ∑ k ∈ cut, wt k := by
    unfold cut
    rw [Finset.sum_image]
    intro i _ j _ he
    exact S.boundary.injective he
  have hcharge : (∑ i : Fin S.count,
      if wt (S.boundary i) < 2 then wt (cyclicSucc (S.boundary i)) else 0) =
      ∑ k ∈ charge, wt k := by
    unfold charge
    rw [Finset.sum_image]
    · simp [light,Finset.sum_filter]
    · intro i _ j _ he
      exact S.boundary.injective (ContactCyclicRestriction.contactCyclicSucc_injective he)
  calc
    2 * S.count = ∑ _i : Fin S.count, (2 : ℕ) := by simp [Nat.mul_comm]
    _ ≤ ∑ i : Fin S.count, (wt (S.boundary i) +
        if wt (S.boundary i) < 2 then wt (cyclicSucc (S.boundary i)) else 0) :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ = ∑ k ∈ cut ∪ charge, wt k := by
      rw [Finset.sum_add_distrib,hcut,hcharge,Finset.sum_union hd]
    _ ≤ ∑ k : Fin B.length, wt k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.zero_le _)
    _ = B.twiceWeight := rfl

end ContactRunSegments
end StructuralRamsey.Girth

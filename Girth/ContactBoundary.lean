import Girth.ContactConstituents
import Girth.ContactRunSegments

/-! The boundary-cycle argument of the new preservation proof.
Only the subdivision facts remain external: no constituent or wagon
contains the whole expanded polygon, and a pair of vertices in both
a wagon and a constituent is consecutive in the expanded polygon.
These hypotheses will be proved by actual side subdivision. Unlike
the old proof, the argument uses only actual graph cycles and shared
chords, with no acceptable word or hypothetical supreme replacement. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P U F J R V₀ E₀ I₀ P₀ : Type v}

theorem contactClosedArc_reverse_side {n : ℕ} (hn : 2 ≤ n) (a t : Fin n) :
    contactClosedArc (cyclicSucc a) a t := by
  have ha := a.isLt
  have ht := t.isLt
  have hs := contactSucc_value a
  unfold contactClosedArc
  by_cases h : a.val + 1 < n
  · rw [if_pos h] at hs
    rw [if_neg (by omega)]
    omega
  · rw [if_neg h] at hs
    rw [if_pos (by omega)]
    omega

private theorem cyclicSucc_sq_of_two {n : ℕ} (hn : n = 2) (i : Fin n) :
    cyclicSucc (cyclicSucc i) = i := by
  subst n
  fin_cases i <;> decide

namespace ContactPictureData
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F J R} (A : ContactPictureData D L H)

/-- This is the pair form of the exceptional-wagon-triple observation:
the only nonconsecutive pair in a wagon trace is the pair of outer
points of its inserted triple, which is in no constituent together.
It is enough for ALL the lifting arguments. -/
def ConsecutiveTrace (C : ContactPolygon U R) : Prop :=
  ∀ (p : P) (a : I ⊕ E) (i j : Fin C.length), i ≠ j →
    C.vertex i ∈ H.contactWagonClique (A.core.wagon p) →
    C.vertex j ∈ H.contactWagonClique (A.core.wagon p) →
    C.vertex i ∈ A.constituent a → C.vertex j ∈ A.constituent a →
    cyclicSucc i = j ∨ cyclicSucc j = i

/-- All boundaries lie in the core, since the owners of consecutive
segments are distinct. -/
theorem segment_boundaries_in_core (C : ContactPolygon U R)
    (S : ContactRunSegments C.vertex A.constituent) :
    ∀ k : Fin S.count, C.vertex (S.boundary k) ∈ Set.range A.core.contactMap := by
  intro k
  obtain ⟨i,hi⟩ := (contactSucc_surjective (n := S.count)) k
  rw [← hi]
  exact A.shared_constituent_core _ _ (S.adjacent_ne i)
    (S.right_mem i) (S.left_mem (cyclicSucc i))

/-- An actual nonconstant segment decomposition has at least three
boundaries in the bad-polygon situation. If there are two, their
pair belongs to a wagon and to both constituents, hence is consecutive.
The reverse arc of that side covers the entire polygon. -/
theorem segment_count_three (h2 : D.ContactG2) (C : ContactPolygon U R)
    (S : ContactRunSegments C.vertex A.constituent)
    (ht : A.ConsecutiveTrace C)
    (hno : ∀ a, ¬ ∀ k, C.vertex k ∈ A.constituent a) :
    3 ≤ S.count := by
  classical
  by_contra hnot
  have htwo : S.count = 2 := by have := S.two; omega
  let i : Fin S.count := ⟨0,by omega⟩
  let j := cyclicSucc i
  have hij : i ≠ j := fun he => contactSucc_ne S.two i he.symm
  have hji : cyclicSucc j = i := cyclicSucc_sq_of_two htwo i
  obtain ⟨x,hx⟩ := A.segment_boundaries_in_core C S i
  obtain ⟨y,hy⟩ := A.segment_boundaries_in_core C S j
  have hxy : x ≠ y := by
    intro he
    apply hij
    apply S.boundary.injective
    exact C.vertex_injective (hx.symm.trans ((congrArg A.core.contactMap he).trans hy))
  have hxi : C.vertex (S.boundary i) ∈ A.constituent (S.owner i) := S.left_mem i
  have hyi : C.vertex (S.boundary j) ∈ A.constituent (S.owner i) := S.right_mem i
  have hxj : C.vertex (S.boundary i) ∈ A.constituent (S.owner j) := by
    have hh := S.right_mem j
    rw [hji] at hh
    exact hh
  have hyj : C.vertex (S.boundary j) ∈ A.constituent (S.owner j) := S.left_mem j
  obtain ⟨p,hxp,hyp⟩ := A.core_constituent_shared_pair h2 (S.owner i) (S.owner j)
    (S.adjacent_ne i) hxy
    ((A.core_constituent_iff _ _).mp (by rw [hx]; exact hxi))
    ((A.core_constituent_iff _ _).mp (by rw [hy]; exact hyi))
    ((A.core_constituent_iff _ _).mp (by rw [hx]; exact hxj))
    ((A.core_constituent_iff _ _).mp (by rw [hy]; exact hyj))
  have hxW : C.vertex (S.boundary i) ∈ H.contactWagonClique (A.core.wagon p) := by
    rw [← hx]
    exact A.core.wagon_clique_preserve p hxp
  have hyW : C.vertex (S.boundary j) ∈ H.contactWagonClique (A.core.wagon p) := by
    rw [← hy]
    exact A.core.wagon_clique_preserve p hyp
  rcases ht p (S.owner i) (S.boundary i) (S.boundary j)
      (fun he => hij (S.boundary.injective he)) hxW hyW hxi hyi with hh | hh
  · apply hno (S.owner j)
    intro k
    apply S.arc_mem j
    rw [hji,← hh]
    exact contactClosedArc_reverse_side (by have := C.hlength; omega) _ _
  · apply hno (S.owner i)
    intro k
    exact S.arc_mem i k (by
      change contactClosedArc (S.boundary i) (S.boundary j) k
      rw [← hh]
      exact contactClosedArc_reverse_side (by have := C.hlength; omega) _ _)

/-- Core contraction of the actual boundary cycle. The weight estimate
is the pure two-sort cyclic restriction inequality. -/
noncomputable def boundaryPolygon (C : ContactPolygon U R)
    (S : ContactRunSegments C.vertex A.constituent) (h3 : 3 ≤ S.count) :
    ContactPolygon V P := by
  classical
  have h := A.segment_boundaries_in_core C S
  let f : Fin S.count → V ⊕ P := fun k => Classical.choose (h k)
  have hf : ∀ k, A.core.contactMap (f k) = C.vertex (S.boundary k) :=
    fun k => Classical.choose_spec (h k)
  exact {
    length := S.count
    hlength := h3
    vertex := f
    vertex_injective := by
      intro i j he
      apply S.boundary.injective
      exact C.vertex_injective ((hf i).symm.trans ((congrArg A.core.contactMap he).trans (hf j)))
  }

theorem boundaryPolygon_lift (C : ContactPolygon U R)
    (S : ContactRunSegments C.vertex A.constituent) (h3 : 3 ≤ S.count)
    (i : Fin S.count) :
    A.core.contactMap ((A.boundaryPolygon C S h3).vertex i) = C.vertex (S.boundary i) :=
  Classical.choose_spec (A.segment_boundaries_in_core C S i)

theorem boundaryPolygon_left (C : ContactPolygon U R)
    (S : ContactRunSegments C.vertex A.constituent) (h3 : 3 ≤ S.count)
    (i : Fin S.count) :
    (A.boundaryPolygon C S h3).vertex i ∈ A.coreConstituent (S.owner i) := by
  apply (A.core_constituent_iff _ _).mp
  rw [A.boundaryPolygon_lift C S h3 i]
  exact S.left_mem i

theorem boundaryPolygon_right (C : ContactPolygon U R)
    (S : ContactRunSegments C.vertex A.constituent) (h3 : 3 ≤ S.count)
    (i : Fin S.count) :
    (A.boundaryPolygon C S h3).vertex (cyclicSucc i) ∈ A.coreConstituent (S.owner i) := by
  apply (A.core_constituent_iff _ _).mp
  exact (A.boundaryPolygon_lift C S h3 (cyclicSucc i)).symm ▸ S.right_mem i

theorem boundaryPolygon_cycle (C : ContactPolygon U R)
    (S : ContactRunSegments C.vertex A.constituent) (h3 : 3 ≤ S.count) :
    (A.boundaryPolygon C S h3).IsCycle D.contactClique := by
  intro i
  obtain ⟨a,ha⟩ := A.core_constituent_cover (S.owner i)
  exact ⟨fun he => contactSucc_ne S.two i
    ((A.boundaryPolygon C S h3).vertex_injective he).symm,
    a,ha (A.boundaryPolygon_left C S h3 i),ha (A.boundaryPolygon_right C S h3 i)⟩

theorem boundaryPolygon_weight (C : ContactPolygon U R)
    (S : ContactRunSegments C.vertex A.constituent) (h3 : 3 ≤ S.count) :
    (A.boundaryPolygon C S h3).twiceWeight ≤ C.twiceWeight := by
  have he : (A.boundaryPolygon C S h3).twiceWeight =
      (C.restrict h3 S.boundary).twiceWeight := by
    unfold ContactPolygon.twiceWeight
    apply Finset.sum_congr rfl
    intro i _
    change contactWeight ((A.boundaryPolygon C S h3).vertex i)
      ((A.boundaryPolygon C S h3).vertex (cyclicSucc i)) =
      contactWeight (C.vertex (S.boundary i)) (C.vertex (S.boundary (cyclicSucc i)))
    exact (A.core_contact_weight ((A.boundaryPolygon C S h3).vertex i)
      ((A.boundaryPolygon C S h3).vertex (cyclicSucc i))).symm.trans
        (congrArg₂ contactWeight (A.boundaryPolygon_lift C S h3 i)
          (A.boundaryPolygon_lift C S h3 (cyclicSucc i)))
  rw [he]
  exact C.restrict_weight_le h3 S.boundary

/-- If a boundary pair is in two distinct generating cliques, it
belongs to one wagon and at least one of the cliques is a copy clique.
The pair form of the trace lemma makes it consecutive in the full
polygon and hence in the boundary polygon. -/
theorem boundary_no_shared_chord (hlin : D.ContactLinear) (h2 : D.ContactG2)
    (C : ContactPolygon U R) (S : ContactRunSegments C.vertex A.constituent)
    (h3 : 3 ≤ S.count) (ht : A.ConsecutiveTrace C) :
    ¬ (A.boundaryPolygon C S h3).HasSharedChord D.contactClique := by
  classical
  rintro ⟨i,j,hnc,a,b,hab,hia,hja,hib,hjb⟩
  let B := A.boundaryPolygon C S h3
  have hne : B.vertex i ≠ B.vertex j := fun he => hnc.1 (B.vertex_injective he)
  obtain ⟨p,hpi,hpj⟩ := D.contact_shared_pair_in_wagon h2 hab hne hia hja hib hjb
  have hcopy : ∃ k : I, B.vertex i ∈ D.contactCopyClique k ∧
      B.vertex j ∈ D.contactCopyClique k := by
    cases a with
    | inl k => exact ⟨k,hia,hja⟩
    | inr r =>
      cases b with
      | inl k => exact ⟨k,hib,hjb⟩
      | inr s =>
        have hr := D.contact_wagon_unique_of_pair hlin hne hia hja hib hjb
        exact (hab (congrArg Sum.inr hr)).elim
  obtain ⟨k,hki,hkj⟩ := hcopy
  have hWi : C.vertex (S.boundary i) ∈ H.contactWagonClique (A.core.wagon p) := by
    rw [← A.boundaryPolygon_lift C S h3 i]
    exact A.core.wagon_clique_preserve p hpi
  have hWj : C.vertex (S.boundary j) ∈ H.contactWagonClique (A.core.wagon p) := by
    rw [← A.boundaryPolygon_lift C S h3 j]
    exact A.core.wagon_clique_preserve p hpj
  have hCi : C.vertex (S.boundary i) ∈ A.constituent (Sum.inl k) := by
    rw [← A.boundaryPolygon_lift C S h3 i]
    exact (A.core_constituent_iff _ _).mpr hki
  have hCj : C.vertex (S.boundary j) ∈ A.constituent (Sum.inl k) := by
    rw [← A.boundaryPolygon_lift C S h3 j]
    exact (A.core_constituent_iff _ _).mpr hkj
  rcases ht p (Sum.inl k) (S.boundary i) (S.boundary j)
      (fun he => hnc.1 (S.boundary.injective he)) hWi hWj hCi hCj with hh | hh
  · exact hnc.2.1
      (ContactCyclicRestriction.successor_of_source_successor S.boundary i j hh.symm).symm
  · exact hnc.2.2
      (ContactCyclicRestriction.successor_of_source_successor S.boundary j i hh.symm).symm

/-- Lifting a covered boundary cycle is impossible. The wagon case
and copy case use the same argument: each segment outside the covering
constituent is a single side of the expanded polygon. -/
theorem boundary_not_covered (h2 : D.ContactG2)
    (C : ContactPolygon U R) (S : ContactRunSegments C.vertex A.constituent)
    (h3 : 3 ≤ S.count) (ht : A.ConsecutiveTrace C)
    (hno : ∀ a, ¬ ∀ k, C.vertex k ∈ A.constituent a)
    (hWno : ∀ p : P, ¬ ∀ k, C.vertex k ∈ H.contactWagonClique (A.core.wagon p)) :
    ¬ (A.boundaryPolygon C S h3).Covered D.contactClique := by
  classical
  rintro ⟨a,ha⟩
  let B := A.boundaryPolygon C S h3
  have hd : ∀ i : Fin S.count, S.boundary i ≠ S.boundary (cyclicSucc i) :=
    fun i he => contactSucc_ne S.two i (S.boundary.injective he).symm
  have hn : 2 ≤ C.length := by have := C.hlength; omega
  cases a with
  | inr p =>
    have hw : ∀ i, C.vertex (S.boundary i) ∈ H.contactWagonClique (A.core.wagon p) := by
      intro i
      rw [← A.boundaryPolygon_lift C S h3 i]
      exact A.core.wagon_clique_preserve p (ha i)
    apply hWno p
    intro k
    obtain ⟨i,hi⟩ := S.arc_cover k
    have he := S.forward_of_consecutive h3 i
      (ht p (S.owner i) _ _ (hd i) (hw i) (hw (cyclicSucc i))
        (S.left_mem i) (S.right_mem i))
    rw [← he] at hi
    rcases contactClosedArc_short hn _ _ hi with hh | hh
    · rw [hh]
      exact hw i
    · rw [hh,he]
      exact hw (cyclicSucc i)
  | inl j =>
    have hc : ∀ i, C.vertex (S.boundary i) ∈ A.constituent (Sum.inl j) := by
      intro i
      rw [← A.boundaryPolygon_lift C S h3 i]
      exact (A.core_constituent_iff _ _).mpr (ha i)
    apply hno (Sum.inl j)
    intro k
    obtain ⟨i,hi⟩ := S.arc_cover k
    by_cases he : S.owner i = Sum.inl j
    · simpa only [he] using S.arc_mem i k hi
    · have hne : B.vertex i ≠ B.vertex (cyclicSucc i) := fun he' =>
        contactSucc_ne S.two i (B.vertex_injective he').symm
      obtain ⟨p,hp,hp'⟩ := A.core_constituent_shared_pair h2 (S.owner i) (Sum.inl j)
        he hne (A.boundaryPolygon_left C S h3 i) (A.boundaryPolygon_right C S h3 i)
        (ha i) (ha (cyclicSucc i))
      have hpL : C.vertex (S.boundary i) ∈ H.contactWagonClique (A.core.wagon p) := by
        rw [← A.boundaryPolygon_lift C S h3 i]
        exact A.core.wagon_clique_preserve p hp
      have hpR : C.vertex (S.boundary (cyclicSucc i)) ∈ H.contactWagonClique (A.core.wagon p) := by
        rw [← A.boundaryPolygon_lift C S h3 (cyclicSucc i)]
        exact A.core.wagon_clique_preserve p hp'
      have hh := S.forward_of_consecutive h3 i
        (ht p (S.owner i) _ _ (hd i) hpL hpR (S.left_mem i) (S.right_mem i))
      rw [← hh] at hi
      rcases contactClosedArc_short hn _ _ hi with hk | hk
      · rw [hk]
        exact hc i
      · rw [hk,hh]
        exact hc (cyclicSucc i)

/-- The contradiction after segment construction. In the positive
cut case G4 supplies the alternative; at the bottom cut the selected
join tree supplies the same alternative. -/
theorem boundary_contradiction (hlin : D.ContactLinear) (h2 : D.ContactG2)
    (C : ContactPolygon U R) (S : ContactRunSegments C.vertex A.constituent)
    (ht : A.ConsecutiveTrace C)
    (hno : ∀ a, ¬ ∀ k, C.vertex k ∈ A.constituent a)
    (hWno : ∀ p : P, ¬ ∀ k, C.vertex k ∈ H.contactWagonClique (A.core.wagon p))
    (halt : ∀ h3 : 3 ≤ S.count, (A.boundaryPolygon C S h3).Covered D.contactClique ∨
      (A.boundaryPolygon C S h3).HasSharedChord D.contactClique) : False := by
  have h3 := A.segment_count_three h2 C S ht hno
  rcases halt h3 with h | h
  · exact A.boundary_not_covered h2 C S h3 ht hno hWno h
  · exact A.boundary_no_shared_chord hlin h2 C S h3 ht h

theorem boundary_contradiction_of_G4 {q : ℕ} (hlin : D.ContactLinear)
    (h2 : D.ContactG2) (h4 : ContactG4 D.contactClique q)
    (C : ContactPolygon U R) (S : ContactRunSegments C.vertex A.constituent)
    (hw : C.twiceWeight ≤ 2*q) (ht : A.ConsecutiveTrace C)
    (hno : ∀ a, ¬ ∀ k, C.vertex k ∈ A.constituent a)
    (hWno : ∀ p : P, ¬ ∀ k, C.vertex k ∈ H.contactWagonClique (A.core.wagon p)) :
    False := by
  apply A.boundary_contradiction hlin h2 C S ht hno hWno
  intro h3
  exact contactSharedChordBound_of_G4 h4 _ (A.boundaryPolygon_cycle C S h3)
    ((A.boundaryPolygon_weight C S h3).trans hw)

end ContactPictureData
end StructuralRamsey.Girth

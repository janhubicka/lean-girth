import Girth.ContactBergeWindows

/-! G3 can be recovered from G4 and the local wagon-girth bounds.
This is the last paragraph of the picture preservation proof, independent
of the segmentation and of the particular free-amalgam construction. -/

namespace StructuralRamsey.Girth

universe v
variable {V E I P : Type v}

namespace OrderOneData
variable (D : OrderOneData V E I P)

/-- Every globally shortest Berge cycle in a linear pretrain of length
within the G4 budget has all its connectors in one designated copy.
No ambient G3 assumption is used. -/
theorem contact_shortest_cycle_in_copy {q : ℕ}
    (hlin : D.ContactLinear) (h2 : D.ContactG2) (h4 : ContactG4 D.contactClique q)
    (B : LabelledBergeCycle D.contactWagonCarrier) (hn : 3 ≤ B.length)
    (hq : B.length ≤ q)
    (hmin : ∀ C : LabelledBergeCycle D.contactWagonCarrier, B.length ≤ C.length) :
    ∃ i, ∀ k, B.vertex k ∈ D.copyCarrier i := by
  classical
  let C : ContactPolygon V P := {
    length := B.length
    hlength := hn
    vertex := fun k => Sum.inl (B.vertex k)
    vertex_injective := fun _ _ h => B.vertex_injective (Sum.inl.inj h)
  }
  have h2len : 2 ≤ B.length := by omega
  have hc : C.IsCycle D.contactClique := by
    intro k
    exact ⟨fun he => contactSucc_ne h2len k (B.vertex_injective (Sum.inl.inj he)).symm,
      Sum.inr (B.label (cyclicSucc k)),B.right_mem k,B.left_mem (cyclicSucc k)⟩
  have hw : C.twiceWeight ≤ 2*q := by
    have hweight : C.twiceWeight = 2*B.length := by
      simp [ContactPolygon.twiceWeight,C,contactWeight,contactKind,
        twiceOccurrenceWeight,Nat.mul_comm]
    omega
  have hwin := B.contact_shortest_window D.contactWagonCarrier hmin hlin.2 hn
  rcases contactSharedChordBound_of_G4 h4 C hc hw with hcover | hchord
  · obtain ⟨a,ha⟩ := hcover
    cases a with
    | inl i => exact ⟨i,ha⟩
    | inr p =>
      obtain ⟨k,hk⟩ := hwin p
      have hx : B.vertex (cyclicSucc (cyclicSucc k)) ∈ D.contactWagonCarrier p :=
        ha (cyclicSucc (cyclicSucc k))
      rcases hk _ hx with he | he
      · exact (contactSucc_sq_ne hn k he).elim
      · exact (contactSucc_ne h2len (cyclicSucc k) he).elim
  · obtain ⟨i,j,hnc,a,b,hab,hia,hja,hib,hjb⟩ := hchord
    obtain ⟨p,hip,hjp⟩ := D.contact_shared_pair_in_wagon h2 hab
      (fun he => hnc.1 (C.vertex_injective he)) hia hja hib hjb
    obtain ⟨k,hk⟩ := hwin p
    have hi := hk i hip
    have hj := hk j hjp
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact (hnc.1 (hi.trans hj.symm)).elim
    · exact (hnc.2.1 (by rw [hi,hj])).elim
    · exact (hnc.2.2 (by rw [hi,hj])).elim
    · exact (hnc.1 (hi.trans hj.symm)).elim

/-- Under G1, the cycle also meets the designated copy in actual edges
of each of its wagon labels. This is needed to contract the cycle. -/
theorem contact_cycle_wagons_meet_copy
    (h1 : D.ContactG1) (B : LabelledBergeCycle D.contactWagonCarrier)
    (i : I) (hi : ∀ k, B.vertex k ∈ D.copyCarrier i) :
    ∀ k, D.contactMeets i (B.label k) := by
  intro k
  obtain ⟨j,hj⟩ := (contactSucc_surjective (n := B.length)) k
  have hne : j ≠ k := by
    intro he
    exact contactSucc_ne B.hlength j (hj.trans he.symm)
  have hWj : B.vertex j ∈ D.contactWagonCarrier (B.label k) := by
    simpa only [hj] using B.right_mem j
  obtain ⟨e,he,hp,_⟩ := h1.bridge i (B.label k)
    (Or.inr ⟨B.vertex j,⟨hi j,hWj⟩,B.vertex k,⟨hi k,B.left_mem k⟩,
      fun he => hne (B.vertex_injective he)⟩) (B.vertex k) (hi k) (B.left_mem k)
  exact ⟨e,he,hp⟩

/-- G3 follows once no short labelled wagon cycle is supported by one
designated copy. In applications the latter is proved by contraction
to an old standard copy. -/
theorem contact_g3_of_local {q : ℕ}
    (hlin : D.ContactLinear) (h2 : D.ContactG2) (h4 : ContactG4 D.contactClique q)
    (hloc : ∀ B : LabelledBergeCycle D.contactWagonCarrier, B.length ≤ q →
      ∀ i, (∀ k, B.vertex k ∈ D.copyCarrier i) → False) :
    LabelledGirthGT D.contactWagonCarrier q := by
  classical
  by_contra hn
  obtain ⟨B,h3,hq,hmin⟩ := LabelledGirthGT.contact_exists_minimal_three_of_failure
    D.contactWagonCarrier q hlin.2 hn
  obtain ⟨i,hi⟩ := D.contact_shortest_cycle_in_copy hlin h2 h4 B h3 hq hmin
  exact hloc B hq i hi

end OrderOneData
end StructuralRamsey.Girth

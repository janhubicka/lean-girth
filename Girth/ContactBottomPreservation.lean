import Girth.ContactBottomOwners
import Girth.ContactPositivePreservation

/-! Assemble the bottom-core preservation alternative.
The special owner assignment eliminates every single mixed-side
segment. The used core pieces have a join tree by the mixed-forest
hypothesis. No ambient G4 or G3 bound on the bottom core is assumed. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I U F R V₀ E₀ I₀ P₀ : Type v}

namespace ContactPictureCopies
variable {D : OrderOneData V E I E} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} {A : ContactPictureData D L H}
    (C : ContactPictureCopies A)

theorem preserves_g4_bottom {q : ℕ}
    (h0 : ∀ e, D.parent e = e) (hinj : Function.Injective H.parent)
    (habs : A.BottomAbsorption)
    (hlin : D.ContactLinear) (h1 : D.ContactG1) (h2 : D.ContactG2)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial)
    (hforest : D.ZeroJoinTreesThrough q)
    (htwo : ∀ i r x y, x ≠ y → x ∈ A.standard i → y ∈ A.standard i →
      x ∈ H.contactWagonCarrier r → y ∈ H.contactWagonCarrier r → A.meets i r)
    (hlocal : ContactG4 L.contactClique q) :
    ContactG4 H.contactClique q := by
  classical
  apply contactG4_of_no_bad
  intro B hw hb
  obtain ⟨out,hout,hforward,hback⟩ := C.bottom_owner_assignment h0 hinj habs B hb
  let owner : Fin B.length → I ⊕ E := fun k => out (contactPrev k)
  have hm : ∀ k, B.vertex k ∈ A.constituent (owner k) ∧
      B.vertex k ∈ A.constituent (owner (cyclicSucc k)) := by
    intro k
    constructor
    · change B.vertex k ∈ A.constituent (out (contactPrev k))
      have h := (hout (contactPrev k)).2
      rw [contactSucc_prev] at h
      exact h
    · change B.vertex k ∈ A.constituent (out (contactPrev (cyclicSucc k)))
      rw [contactPrev_succ]
      exact (hout k).1
  have hnon : ¬ ∃ a, ∀ k, owner k = a := by
    rintro ⟨a,ha⟩
    have hc : ∀ k, B.vertex k ∈ A.constituent a := by
      intro k
      have h := (hm k).1
      rw [ha k] at h
      exact h
    cases a with
    | inl i => exact C.bad_not_in_standard h1 h2 htwo hlocal B hw hb i hc
    | inr e =>
      exact hb.2.1 ⟨Sum.inr (A.core.wagon (D.parent e)),
        fun k => A.enlarged_edge_subset_wagon e (hc k)⟩
  let S := contactSegments_of_owners (by have := B.hlength; omega)
    owner B.vertex A.constituent hm hnon
  have hcut : ∀ i : Fin S.count, out (contactPrev (S.boundary i)) ≠ out (S.boundary i) := by
    intro i
    have h := contactOwnerCutIndex_is_change owner i
    change owner (S.boundary i) ≠ owner (cyclicSucc (S.boundary i)) at h
    simpa only [owner,contactPrev_succ] using h
  apply C.bottom_bad_contradiction h0 hlin h1 h2 hsize hforest htwo hlocal B hw hb S
  intro i hi
  let k := S.boundary i
  have hkCore := A.segment_boundaries_in_core B S i
  have hsCore := A.segment_boundaries_in_core B S (cyclicSucc i)
  change S.boundary (cyclicSucc i) = cyclicSucc k at hi
  rw [hi] at hsCore
  change B.vertex k ∈ Set.range A.core.contactMap at hkCore
  obtain ⟨a,ha⟩ := hkCore
  obtain ⟨b,hb'⟩ := hsCore
  change 2 ≤ contactWeight (B.vertex k) (B.vertex (cyclicSucc k))
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      rw [← ha,← hb']
      rfl
    | inr p =>
      have hf : A.BottomForward B k := ⟨x,p,ha.symm,hb'.symm⟩
      have h := hcut (cyclicSucc i)
      rw [hi,contactPrev_succ] at h
      exact (h (hforward k hf)).elim
  | inr p =>
    cases b with
    | inl x =>
      have hb'' : A.BottomBackward B k := ⟨x,p,ha.symm,hb'.symm⟩
      exact (hcut i (hback k hb'').symm).elim
    | inr r =>
      rw [← ha,← hb']
      rfl

/-- System girth at the bottom cut, from the two-member intersection
property and selected join trees of the core. The input absorption
is exactly the one-edge trace property on the active strip. -/
theorem preserves_systemGirth_bottom {q : ℕ}
    (h0 : ∀ e, D.parent e = e) (hinj : Function.Injective H.parent)
    (habs : A.BottomAbsorption) (hc : A.CoreStrong)
    (hp : D.ZeroPairwise)
    (hsub : ∀ i e, e ∈ D.copyEdges i → D.edgeCarrier e ⊆ D.copyCarrier i)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial)
    (hforest : D.ZeroJoinTreesThrough q)
    (hL : L.ContactSystemGirthGT q) :
    H.ContactSystemGirthGT q := by
  have hlinD := D.zero_linearity_of_pairwise h0 hp
  have h1 := D.zero_g1_of_pairwise h0 hp hsub
  have h2 := D.zero_g2_of_pairwise h0 hp h1 hlinD hsize
  have hs := A.standard_strong hc h1
  have hE := A.edge_linearity hc hs hlinD hL.linear
  have hW : ∀ r s : R, r ≠ s →
      (H.contactWagonCarrier r ∩ H.contactWagonCarrier s).Subsingleton := by
    intro r s hne
    obtain ⟨e,rfl⟩ := A.parent_surjective r
    obtain ⟨f,rfl⟩ := A.parent_surjective s
    rw [A.bottom_wagon_eq_edge hinj,A.bottom_wagon_eq_edge hinj]
    exact hE e f (fun he => hne (congrArg H.parent he))
  have hlin : H.ContactLinear := ⟨hE,hW⟩
  have ht := A.twoPoint_of_parent_injective hinj hs
  have h1' := C.preserves_g1 h1 h2 hL.g1 hs ht
  have h2' := C.preserves_g2 h2 hL.g2
  have h4 := C.preserves_g4_bottom h0 hinj habs hlinD h1 h2 hsize hforest ht hL.g4
  exact ⟨hlin,h1',h2',C.preserves_g3_of_g4 h1 h2 h1' h2' hlin h4 hL.g3,h4⟩

end ContactPictureCopies
end StructuralRamsey.Girth

import Girth.ContactBottomCore
import Girth.ContactZeroJoinTrees
import Girth.ContactSegmentBudget
import Girth.ContactBoundary
import Girth.ContactSideSubdivision

/-! The bottom core alternative: a selected join tree supplies the
covered/shared-chord alternative for the contracted boundary cycle.
The only remaining geometric obligation here is the special bottom
side assignment that prevents a single mixed-side segment. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I U F R V₀ E₀ I₀ P₀ : Type v}



namespace ContactPictureData
variable {D : OrderOneData V E I E} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} (A : ContactPictureData D L H)

theorem zero_coreConstituent_eq (h0 : ∀ e, D.parent e = e) (a : I ⊕ E) :
    A.coreConstituent a = D.contactClique a := by
  cases a with
  | inl i => rfl
  | inr e =>
    ext z
    cases z with
    | inl x =>
      change x ∈ D.edgeCarrier e ↔ x ∈ D.contactWagonCarrier e
      rw [D.zero_wagonCarrier_eq h0]
    | inr p =>
      change p = D.parent e ↔ p = e
      rw [h0]

/-- Construct the finite family of used segment labels and its
selected join tree. This supplies the boundary alternative without
any global G4 assumption on the bottom core. -/
theorem zero_boundary_alternative {q : ℕ} (h0 : ∀ e, D.parent e = e)
    (hlin : D.ContactLinear) (h1 : D.ContactG1)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial)
    (hforest : D.ZeroJoinTreesThrough q)
    (B : ContactPolygon U R) (S : ContactRunSegments B.vertex A.constituent)
    (h3 : 3 ≤ S.count) (hbudget : S.count ≤ q) (hw : B.twiceWeight ≤ 2*q) :
    (A.boundaryPolygon B S h3).Covered D.contactClique ∨
      (A.boundaryPolygon B S h3).HasSharedChord D.contactClique := by
  classical
  let s : Finset (I ⊕ E) := Finset.univ.image S.owner
  let Q := A.boundaryPolygon B S h3
  have hcard : s.card ≤ q := by
    calc
      s.card ≤ (Finset.univ : Finset (Fin S.count)).card := Finset.card_image_le
      _ = S.count := by simp
      _ ≤ q := hbudget
  have hne : s.Nonempty := by
    let i : Fin S.count := ⟨0,by omega⟩
    exact ⟨S.owner i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  obtain ⟨T⟩ := hforest s hne hcard
  let own : Fin S.count → {a // a ∈ s} := fun i =>
    ⟨S.owner i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  let K : {a // a ∈ s} → Set (V ⊕ E) := fun a => D.contactClique a.val
  have hg : ContactG4 K q := D.zero_selected_g4 Subtype.val h0 h1 hlin hsize T q
  have hc : Q.IsCycle K := by
    intro i
    have hleft := A.boundaryPolygon_left B S h3 i
    have hright := A.boundaryPolygon_right B S h3 i
    rw [A.zero_coreConstituent_eq h0] at hleft hright
    refine ⟨?_,own i,hleft,hright⟩
    intro he
    exact contactSucc_ne S.two i (Q.vertex_injective he).symm
  rcases contactSharedChordBound_of_G4 hg Q hc
      ((A.boundaryPolygon_weight B S h3).trans hw) with h | h
  · obtain ⟨a,ha⟩ := h
    exact Or.inl ⟨a.val,ha⟩
  · obtain ⟨i,j,hnc,a,b,hab,h1,h2,h3',h4⟩ := h
    exact Or.inr ⟨i,j,hnc,a.val,b.val,fun he => hab (Subtype.ext he),h1,h2,h3',h4⟩

end ContactPictureData

namespace ContactPictureCopies
variable {D : OrderOneData V E I E} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} {A : ContactPictureData D L H}
    (C : ContactPictureCopies A)
include C

/-- The full bottom boundary contradiction from an actual segment
decomposition satisfying the single-mixed-side exclusion.
The special choice of bottom owners remains to be constructed. -/
theorem bottom_bad_contradiction {q : ℕ}
    (h0 : ∀ e, D.parent e = e) (hlin : D.ContactLinear)
    (h1 : D.ContactG1) (h2 : D.ContactG2)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial)
    (hforest : D.ZeroJoinTreesThrough q)
    (htwo : ∀ i r x y, x ≠ y → x ∈ A.standard i → y ∈ A.standard i →
      x ∈ H.contactWagonCarrier r → y ∈ H.contactWagonCarrier r → A.meets i r)
    (hlocal : ContactG4 L.contactClique q)
    (B : ContactPolygon U R) (hw : B.twiceWeight ≤ 2*q)
    (hb : B.Bad H.contactClique)
    (S : ContactRunSegments B.vertex A.constituent)
    (hheavy : ∀ i : Fin S.count,
      S.boundary (cyclicSucc i) = cyclicSucc (S.boundary i) →
      2 ≤ contactWeight (B.vertex (S.boundary i))
        (B.vertex (cyclicSucc (S.boundary i)))) :
    False := by
  have ht : A.ConsecutiveTrace B := by
    intro p a i j hij hi hj _ _
    exact B.consecutive_of_no_chord hb.2.2 hij
      ⟨fun he => hij (B.vertex_injective he),Sum.inr (A.core.wagon p),hi,hj⟩
  have hWno : ∀ p : E, ¬ ∀ k, B.vertex k ∈ H.contactWagonClique (A.core.wagon p) :=
    fun p h => hb.2.1 ⟨Sum.inr (A.core.wagon p),h⟩
  have hno : ∀ a, ¬ ∀ k, B.vertex k ∈ A.constituent a := by
    intro a h
    cases a with
    | inl i => exact C.bad_not_in_standard h1 h2 htwo hlocal B hw hb i h
    | inr e =>
      exact hWno (D.parent e) (fun k => A.enlarged_edge_subset_wagon e (h k))
  have hcnt := S.count_twice_le_weight hheavy
  have hbudget : S.count ≤ q := by omega
  exact A.boundary_contradiction hlin h2 B S ht hno hWno
    (fun h3 => A.zero_boundary_alternative h0 hlin h1 hsize hforest B S h3 hbudget hw)

end ContactPictureCopies
end StructuralRamsey.Girth

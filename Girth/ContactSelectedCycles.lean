import Girth.ContactLevelZero

/-! The converse mixed-forest argument at the bottom level.
For a selected family of at most q pieces, its real-vertex
two-section has no bad polygon of ANY length. The budget comes
from injectivity of its side owners, not an assumption on length. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I J : Type v}

namespace OrderOneData
variable (D : OrderOneData V E I E)

def zeroRealClique (a : I ⊕ E) : Set (V ⊕ E) :=
  {z | ∃ x : V, z = Sum.inl x ∧ x ∈ D.carrier a}

theorem zeroRealClique_mem (a : I ⊕ E) (x : V) :
    Sum.inl x ∈ D.zeroRealClique a ↔ x ∈ D.carrier a := by
  constructor
  · rintro ⟨y,hy,h⟩
    have he := Sum.inl.inj hy
    simpa only [← he] using h
  · intro h
    exact ⟨x,rfl,h⟩

/-- Each side of a bad polygon lies in a different selected piece:
one piece cannot contain three of its vertices. -/
theorem zero_selected_no_bad [Fintype J] {q : ℕ}
    (h0 : ∀ e, D.parent e = e) (h : D.ContactSystemGirthGT q)
    (sel : J → I ⊕ E) (hcard : Fintype.card J ≤ q)
    (B : ContactPolygon V E)
    (hb : B.Bad (fun j => D.zeroRealClique (sel j))) : False := by
  classical
  have hreal : ∀ k, ∃ x : V, B.vertex k = Sum.inl x := by
    intro k
    obtain ⟨_,a,hk,_⟩ := hb.1 k
    obtain ⟨x,hx,_⟩ := hk
    exact ⟨x,hx⟩
  choose v hv using hreal
  have hvInj : Function.Injective v := by
    intro i j he
    apply B.vertex_injective
    exact (hv i).trans ((congrArg Sum.inl he).trans (hv j).symm)
  have hex : ∀ k, ∃ a : J, B.vertex k ∈ D.zeroRealClique (sel a) ∧
      B.vertex (cyclicSucc k) ∈ D.zeroRealClique (sel a) :=
    fun k => (hb.1 k).2
  choose owner howner using hex
  have hthird : ∀ i j, j ≠ i → j ≠ cyclicSucc i →
      v j ∉ D.carrier (sel (owner i)) := by
    intro i j hji hjs hj
    have h2 : 2 ≤ B.length := by have := B.hlength; omega
    have hm : B.vertex j ∈ D.zeroRealClique (sel (owner i)) :=
      ⟨v j,hv j,hj⟩
    exact B.bad_no_three hb (owner i)
      (fun he => contactSucc_ne h2 i he.symm) (fun he => hji he.symm)
      (fun he => hjs he.symm) (howner i).1 (howner i).2 hm
  have hleft : ∀ i, v i ∈ D.carrier (sel (owner i)) := by
    intro i
    apply (D.zeroRealClique_mem _ _).mp
    rw [← hv i]
    exact (howner i).1
  have hright : ∀ i, v (cyclicSucc i) ∈ D.carrier (sel (owner i)) := by
    intro i
    apply (D.zeroRealClique_mem _ _).mp
    rw [← hv (cyclicSucc i)]
    exact (howner i).2
  have hoInj : Function.Injective owner := by
    intro i j he
    by_contra hne
    have hj : v j ∈ D.carrier (sel (owner i)) := by
      rw [he]
      exact hleft j
    have hji : j = cyclicSucc i := by
      by_contra hn
      exact hthird i j (fun he' => hne he'.symm) hn hj
    have hs : v (cyclicSucc j) ∈ D.carrier (sel (owner i)) := by
      rw [he]
      exact hright j
    have hs₁ : cyclicSucc j ≠ i := by
      rw [hji]
      exact contactSucc_sq_ne B.hlength i
    have hs₂ : cyclicSucc j ≠ cyclicSucc i := fun he' =>
      hne ((ContactCyclicRestriction.contactCyclicSucc_injective he').symm)
    exact hthird i (cyclicSucc j) hs₁ hs₂ hs
  have hbudget : B.length ≤ q := by
    have hc := Fintype.card_le_of_injective owner hoInj
    rw [Fintype.card_fin] at hc
    exact hc.trans hcard
  exact D.zero_no_sparse_polygon h0 h B.hlength hbudget v hvInj
    (sel ∘ owner) hleft hright hthird

theorem zero_selected_real_g4 [Fintype J] {q : ℕ}
    (h0 : ∀ e, D.parent e = e) (h : D.ContactSystemGirthGT q)
    (sel : J → I ⊕ E) (hcard : Fintype.card J ≤ q) (r : ℕ) :
    ContactG4 (fun j => D.zeroRealClique (sel j)) r := by
  apply contactG4_of_no_bad
  intro B _ hb
  exact D.zero_selected_no_bad h0 h sel hcard B hb

end OrderOneData
end StructuralRamsey.Girth

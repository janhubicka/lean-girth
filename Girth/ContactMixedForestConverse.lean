import Girth.ContactConformality
import Girth.ContactJoinTreeCharacterization
import Girth.ContactZeroJoinTrees

/-! The converse passage from bottom system girth to mixed forests.
The selected-family polygon and conformality obstructions supply
the two hypotheses of the independently constructed join-tree
equivalence. The pairwise condition is the checked G1/G2 consequence. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I J : Type v}

namespace OrderOneData
variable (D : OrderOneData V E I E)

/-- The graph on the real vertices of a small selected family
is chordal, without any assumption on the length of a tested
cycle. The previous side-owner injection supplies the budget. -/
theorem zero_selected_chordal [Fintype J] {q : ℕ}
    (h0 : ∀ e, D.parent e = e) (h : D.ContactSystemGirthGT q)
    (sel : J → I ⊕ E) (hcard : Fintype.card J ≤ q) :
    ContactChordal (contactFamilyGraph (fun a => D.carrier (sel a))) := by
  intro n z hn hInj hside
  let K : J → Set (V ⊕ E) := fun a => D.zeroRealClique (sel a)
  let C : ContactPolygon V E := {
    length := n
    hlength := by omega
    vertex := fun i => Sum.inl (z i)
    vertex_injective := fun _ _ he => hInj (Sum.inl.inj he)
  }
  have hc : C.IsCycle K := by
    intro i
    obtain ⟨hne,a,ha,hb⟩ := hside i
    exact ⟨fun he => hne (Sum.inl.inj he),a,
      (D.zeroRealClique_mem _ _).mpr ha,(D.zeroRealClique_mem _ _).mpr hb⟩
  have hw : C.twiceWeight ≤ 2*n := by
    simp [ContactPolygon.twiceWeight,C,contactWeight,contactKind,
      twiceOccurrenceWeight,Nat.mul_comm]
  obtain ⟨i,j,hnc,hne,a,ha,hb⟩ :=
    ((D.zero_selected_real_g4 h0 h sel hcard n) C hc hw).2 hn
  exact ⟨i,j,hnc.1,hnc.2.1,hnc.2.2,
    fun he => hne (congrArg Sum.inl he),a,
    (D.zeroRealClique_mem _ _).mp ha,(D.zeroRealClique_mem _ _).mp hb⟩

theorem zero_selected_joinTree [Fintype V] [Fintype J] [Nonempty J] {q : ℕ}
    (h0 : ∀ e, D.parent e = e) (h : D.ContactSystemGirthGT q)
    (sel : J → I ⊕ E) (hcard : Fintype.card J ≤ q) :
    Nonempty (ContactJoinTree (fun a => D.carrier (sel a))) := by
  apply contact_joinTree_of_chordal_conformal
  · exact D.zero_selected_chordal h0 h sel hcard
  · intro s hs hv hp
    exact D.zero_selected_conformal h0 h sel hcard s hs hv hp

/-- The whole mixed-forest conclusion of the manuscript's
level-zero system-girth lemma, including the actual join trees. -/
theorem zero_mixedForests_of_systemGirth [Fintype V] {q : ℕ}
    (h0 : ∀ e, D.parent e = e) (h : D.ContactSystemGirthGT q) :
    D.ZeroMixedForestsThrough q := by
  classical
  refine ⟨D.zero_pairwise_allowed h0 h.linear h.g1 h.g2,?_⟩
  intro s hs hcard
  let J := {a // a ∈ s}
  letI : Nonempty J := by obtain ⟨a,ha⟩ := hs; exact ⟨⟨a,ha⟩⟩
  have hj : Fintype.card J ≤ q := by
    simpa [J] using hcard
  exact D.zero_selected_joinTree h0 h Subtype.val hj

end OrderOneData
end StructuralRamsey.Girth

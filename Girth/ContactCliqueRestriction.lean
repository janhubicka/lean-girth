import Girth.ContactBadCycle

/-! Abstract copy restriction, at the level of generating cliques.
The stable cliques are the wagon cliques. The old copy cliques are
partitioned into component cliques and each component is shrunk.
Only two local facts are needed: stable pairs do not cross components
of the same old copy, and discarded vertices have their neighbours
in at most one stable clique within the component. -/

namespace StructuralRamsey.Girth

universe v
variable {V P I J : Type v}

def contactFamily (copies : I → Set (V ⊕ P)) (wagons : P → Set (V ⊕ P)) :
    I ⊕ P → Set (V ⊕ P)
  | .inl i => copies i
  | .inr p => wagons p

structure ContactCliqueRestriction (old : I → Set (V ⊕ P))
    (stable : P → Set (V ⊕ P)) (new : J → Set (V ⊕ P)) where
  parent : J → I
  component : J → Set (V ⊕ P)
  component_sub : ∀ j, component j ⊆ old (parent j)
  component_cover : ∀ i x, x ∈ old i → ∃ j, parent j = i ∧ x ∈ component j
  component_unique : ∀ j k, parent j = parent k →
    ∀ x, x ∈ component j → x ∈ component k → j = k
  retained_sub : ∀ j, new j ⊆ component j
  old_shared : ∀ i i' : I, i ≠ i' → ∀ x y, x ≠ y →
    x ∈ old i → y ∈ old i → x ∈ old i' → y ∈ old i' →
    ∃ p, x ∈ stable p ∧ y ∈ stable p
  stable_pair_component : ∀ j k, parent j = parent k →
    ∀ p x y, x ≠ y → x ∈ component j → y ∈ component k →
      x ∈ stable p → y ∈ stable p → j = k
  omitted_stable_unique : ∀ j x y z p p',
    x ∈ component j → x ∉ new j → y ∈ component j → z ∈ component j →
    x ≠ y → x ≠ z →
    x ∈ stable p → y ∈ stable p → x ∈ stable p' → z ∈ stable p' → p = p'

namespace ContactCliqueRestriction

variable {old : I → Set (V ⊕ P)} {stable : P → Set (V ⊕ P)}
    {new : J → Set (V ⊕ P)} (A : ContactCliqueRestriction old stable new)
include A

theorem adjacency_old {x y : V ⊕ P} (h : contactAdjacent (contactFamily new stable) x y) :
    contactAdjacent (contactFamily old stable) x y := by
  obtain ⟨hne,a,hx,hy⟩ := h
  cases a with
  | inr p => exact ⟨hne,Sum.inr p,hx,hy⟩
  | inl j => exact ⟨hne,Sum.inl (A.parent j),
      A.component_sub j (A.retained_sub j hx),
      A.component_sub j (A.retained_sub j hy)⟩

theorem shared_old_survives (a b : I ⊕ P) (hab : a ≠ b)
    (x y : V ⊕ P) (hxy : x ≠ y)
    (hxa : x ∈ contactFamily old stable a) (hya : y ∈ contactFamily old stable a)
    (hxb : x ∈ contactFamily old stable b) (hyb : y ∈ contactFamily old stable b) :
    contactAdjacent (contactFamily new stable) x y := by
  cases a with
  | inr p => exact ⟨hxy,Sum.inr p,hxa,hya⟩
  | inl i =>
    cases b with
    | inr p => exact ⟨hxy,Sum.inr p,hxb,hyb⟩
    | inl i' =>
      have hii' : i ≠ i' := fun he => hab (congrArg Sum.inl he)
      obtain ⟨p,hx,hy⟩ := A.old_shared i i' hii' x y hxy hxa hya hxb hyb
      exact ⟨hxy,Sum.inr p,hx,hy⟩

/-- Within a single old copy, adjacency in the restricted graph never
crosses its component partition. -/
theorem adjacent_same_component {j k : J} (hpar : A.parent j = A.parent k)
    {x y : V ⊕ P} (hx : x ∈ A.component j) (hy : y ∈ A.component k)
    (h : contactAdjacent (contactFamily new stable) x y) : j = k := by
  classical
  obtain ⟨hxy,a,hxa,hya⟩ := h
  cases a with
  | inr p => exact A.stable_pair_component j k hpar p x y hxy hx hy hxa hya
  | inl l =>
    by_cases he : A.parent j = A.parent l
    · have hjl := A.component_unique j l he x hx (A.retained_sub l hxa)
      have hkl := A.component_unique k l (hpar.symm.trans he) y hy (A.retained_sub l hya)
      exact hjl.trans hkl.symm
    · have hyold : y ∈ old (A.parent j) := by
        rw [hpar]
        exact A.component_sub k hy
      obtain ⟨p,hxp,hyp⟩ := A.old_shared (A.parent j) (A.parent l) he x y hxy
        (A.component_sub j hx) hyold
        (A.component_sub l (A.retained_sub l hxa))
        (A.component_sub l (A.retained_sub l hya))
      exact A.stable_pair_component j k hpar p x y hxy hx hy hxp hyp

/-- An edge touching a discarded point, inside its own old component,
must come from a stable clique. -/
theorem omitted_edge_stable {j : J} {x y : V ⊕ P}
    (hx : x ∈ A.component j) (hy : y ∈ A.component j) (hn : x ∉ new j)
    (h : contactAdjacent (contactFamily new stable) x y) :
    ∃ p, x ∈ stable p ∧ y ∈ stable p := by
  classical
  obtain ⟨hxy,a,hxa,hya⟩ := h
  cases a with
  | inr p => exact ⟨p,hxa,hya⟩
  | inl l =>
    by_cases he : A.parent j = A.parent l
    · have hjl := A.component_unique j l he x hx (A.retained_sub l hxa)
      subst l
      exact (hn hxa).elim
    · exact A.old_shared (A.parent j) (A.parent l) he x y hxy
        (A.component_sub j hx) (A.component_sub j hy)
        (A.component_sub l (A.retained_sub l hxa))
        (A.component_sub l (A.retained_sub l hya))

/-- The full abstract restriction theorem for G4. The proof is just
localization in one old clique, propagation in a single component,
and the fact that a discarded point is simplicial there. -/
theorem preserves_g4 {q : ℕ} (h4 : ContactG4 (contactFamily old stable) q) :
    ContactG4 (contactFamily new stable) q := by
  classical
  apply contactG4_of_no_bad
  intro C hw hb
  obtain ⟨a,ha⟩ := contact_bad_localizes h4
    (fun _ _ h => A.adjacency_old h)
    A.shared_old_survives C hw hb
  cases a with
  | inr p =>
    exact hb.2.1 ⟨Sum.inr p,ha⟩
  | inl i =>
    have hpos : 0 < C.length := by have := C.hlength; omega
    obtain ⟨j,hji,h0⟩ := A.component_cover i (C.vertex ⟨0,hpos⟩) (ha ⟨0,hpos⟩)
    have hall : ∀ k, C.vertex k ∈ A.component j := by
      apply contactCycle_all_of_zero hpos _ h0
      intro k hk
      obtain ⟨l,hli,hl⟩ := A.component_cover i _ (ha (cyclicSucc k))
      have he := A.adjacent_same_component (hji.trans hli.symm) hk hl (hb.1 k)
      simpa only [he] using hl
    apply hb.2.1
    refine ⟨Sum.inl j,?_⟩
    intro k
    by_contra hn
    obtain ⟨b,hb'⟩ := (contactSucc_surjective (n := C.length)) k
    have hn' : C.vertex (cyclicSucc b) ∉ new j := by rw [hb']; exact hn
    have hleft := contactAdjacent_symm (hb.1 b)
    have hright := hb.1 (cyclicSucc b)
    obtain ⟨p,hp,hpb⟩ := A.omitted_edge_stable
      (hall (cyclicSucc b)) (hall b) hn' hleft
    obtain ⟨p',hp',hpn⟩ := A.omitted_edge_stable
      (hall (cyclicSucc b)) (hall (cyclicSucc (cyclicSucc b))) hn' hright
    have he := A.omitted_stable_unique j _ _ _ p p'
      (hall (cyclicSucc b)) hn' (hall b) (hall (cyclicSucc (cyclicSucc b)))
      hleft.1 hright.1 hp hpb hp' hpn
    subst p'
    exact C.bad_no_three_successive hb (Sum.inr p) b hpb hp hpn

end ContactCliqueRestriction
end StructuralRamsey.Girth

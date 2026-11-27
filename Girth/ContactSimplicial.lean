import Girth.ContactMinimalSeparator

/-! A finite chordal graph has a simplicial vertex outside any
proper clique. This stronger induction statement makes the
minimal-separator argument short: at least one of the two full
components is disjoint from the prescribed clique. Induct on
that component together with the separator. -/

namespace StructuralRamsey.Girth
universe v
variable {W : Type v}

def ContactSimplicial (G : SimpleGraph W) (x : W) : Prop :=
  ∀ y z, G.Adj x y → G.Adj x z → y ≠ z → G.Adj y z

def ContactClique (G : SimpleGraph W) (K : Set W) : Prop :=
  ∀ y ∈ K, ∀ z ∈ K, y ≠ z → G.Adj y z

/-- All neighbours of a vertex in a component outside a separator
are in that component or in the separator. -/
theorem contactComponent.neighbour_mem_union {G : SimpleGraph W}
    {a x y : W} {S : Set W}
    (hx : x ∈ contactComponent G Sᶜ a) (hxy : G.Adj x y) :
    y ∈ contactComponent G Sᶜ a ∪ S := by
  classical
  by_cases hy : y ∈ S
  · exact Or.inr hy
  · exact Or.inl (contactComponent.closed hx hy hxy)

/-- Strong induction form of Dirac's simplicial-vertex lemma.
It includes disconnected graphs and an empty prescribed clique. -/
theorem contact_simplicial_outside [Fintype W] (G : SimpleGraph W)
    (hch : ContactChordal G) (K : Set W) (hK : ContactClique G K)
    (hproper : ∃ x, x ∉ K) :
    ∃ x, x ∉ K ∧ ContactSimplicial G x := by
  classical
  have aux : ∀ n : ℕ, ∀ (X : Type v) [Fintype X], Fintype.card X = n →
      ∀ (G : SimpleGraph X), ContactChordal G →
      ∀ K : Set X, ContactClique G K → (∃ x, x ∉ K) →
      ∃ x, x ∉ K ∧ ContactSimplicial G x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X inst hn H hc A hA hproper
      by_cases hcomplete : ∀ a b : X, a ≠ b → H.Adj a b
      · obtain ⟨x,hx⟩ := hproper
        exact ⟨x,hx,fun y z _ _ hne => hcomplete y z hne⟩
      · push_neg at hcomplete
        obtain ⟨a,b,hab,hnab⟩ := hcomplete
        obtain ⟨S⟩ := contact_exists_minimalSeparator H a b hab hnab
        let C : Set X := ↑S.cut
        have hC : ContactClique H C := S.cut_clique hc
        have hchoose : ∃ L : Set X,
            (∃ x, x ∈ L) ∧ Disjoint L C ∧ Disjoint L A ∧
            (∃ y, y ∉ L ∪ C) ∧
            (∀ x ∈ L, ∀ y, H.Adj x y → y ∈ L ∪ C) := by
          by_cases hl : ∃ x, x ∈ S.left ∧ x ∈ A
          · obtain ⟨x,hxl,hxA⟩ := hl
            refine ⟨S.right,⟨b,S.right_root⟩,?_,?_,⟨a,?_⟩,?_⟩
            · apply Set.disjoint_left.mpr
              intro u hu hu'
              exact hu.1 hu'
            · apply Set.disjoint_left.mpr
              intro u hu huA
              have hne : x ≠ u := by
                intro he
                exact Set.disjoint_left.mp S.sides_disjoint hxl (he.symm ▸ hu)
              exact S.sides_no_edge hxl hu (hA x hxA u huA hne)
            · rintro (ha | ha)
              · exact Set.disjoint_left.mp S.sides_disjoint S.left_root ha
              · exact S.separates.1 ha
            · intro u hu y huy
              by_cases hy : y ∈ C
              · exact Or.inr hy
              · exact Or.inl (contactComponent.closed hu hy huy)
          · refine ⟨S.left,⟨a,S.left_root⟩,?_,?_,⟨b,?_⟩,?_⟩
            · apply Set.disjoint_left.mpr
              intro u hu hu'
              exact hu.1 hu'
            · apply Set.disjoint_left.mpr
              intro u hu huA
              exact hl ⟨u,hu,huA⟩
            · rintro (hb | hb)
              · exact Set.disjoint_left.mp S.sides_disjoint hb S.right_root
              · exact S.separates.2.1 hb
            · intro u hu y huy
              by_cases hy : y ∈ C
              · exact Or.inr hy
              · exact Or.inl (contactComponent.closed hu hy huy)
        obtain ⟨L,hL,hLC,hLA,houtside,hclosed⟩ := hchoose
        let U : Set X := L ∪ C
        let X' := {x : X // x ∈ U}
        letI : Fintype X' := Fintype.ofFinite X'
        let K' : Set X' := {x | x.val ∈ C}
        have hlt : Fintype.card X' < n := by
          rw [← hn]
          apply Fintype.card_lt_of_injective_not_surjective (fun x : X' => x.val)
            Subtype.val_injective
          intro hsur
          obtain ⟨y,hy⟩ := houtside
          obtain ⟨z,hz⟩ := hsur y
          exact hy (hz ▸ z.property)
        have hK' : ContactClique (H.induce U) K' := by
          intro y hy z hz hne
          exact hC y.val hy z.val hz (fun he => hne (Subtype.ext he))
        have hproper' : ∃ x : X', x ∉ K' := by
          obtain ⟨x,hx⟩ := hL
          exact ⟨⟨x,Or.inl hx⟩,fun h => Set.disjoint_left.mp hLC hx h⟩
        obtain ⟨x,hx,hxsim⟩ := ih (Fintype.card X') hlt X' rfl
          (H.induce U) (contactChordal_induce hc U) K' hK' hproper'
        have hxL : x.val ∈ L := by
          rcases x.property with hh | hh
          · exact hh
          · exact (hx hh).elim
        refine ⟨x.val,fun h => Set.disjoint_left.mp hLA hxL h,?_⟩
        intro y z hy hz hne
        let y' : X' := ⟨y,hclosed x.val hxL y hy⟩
        let z' : X' := ⟨z,hclosed x.val hxL z hz⟩
        exact hxsim y' z' hy hz (fun he => hne (congrArg Subtype.val he))
  exact aux (Fintype.card W) W rfl G hch K hK hproper

theorem contact_exists_simplicial [Fintype W] [Nonempty W] (G : SimpleGraph W)
    (hch : ContactChordal G) : ∃ x, ContactSimplicial G x := by
  obtain ⟨x,_,hx⟩ := contact_simplicial_outside G hch ∅
    (by intro y hy; exact (False.elim hy)) ⟨Classical.choice inferInstance,by simp⟩
  exact ⟨x,hx⟩

end StructuralRamsey.Girth

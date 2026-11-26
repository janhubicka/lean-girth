import Girth.ContactBergeWindows
import Girth.ContactJoinTree

/-! One marked edge per member of a forest. This is the direct
leaf-deletion proof used by the outer partite construction. The
cycle labels are the actual marked edges, not representatives of
arbitrary equal carrier sets. -/

namespace StructuralRamsey.Girth
universe v
variable {V E : Type v}

/-- A forest of linear support pieces, each containing at most one
marked edge, cannot contain a Berge cycle of marked edges. The
separator of adjacent pieces is an actual common edge or has
at most one vertex. -/
theorem contact_marked_cycle_impossible {Q : Type v} [Fintype Q]
    (carrier : Q → Set V) (edge : E → Set V) (supports : Q → Set E)
    (marked : E → Prop)
    (J : ContactJoinTree carrier)
    (hsub : ∀ i e, e ∈ supports i → edge e ⊆ carrier i)
    (hmark : ∀ i e f, e ∈ supports i → f ∈ supports i →
      marked e → marked f → e = f)
    (hlin : ∀ e f, e ≠ f → (edge e ∩ edge f).Subsingleton)
    (hsep : ∀ i j, i ≠ j →
      (carrier i ∩ carrier j).Subsingleton ∨
        ∃ e, e ∈ supports i ∧ e ∈ supports j ∧
          carrier i ∩ carrier j = edge e)
    (C : LabelledBergeCycle (fun e : {e : E // marked e} => edge e.val))
    (hcover : ∀ k, ∃ i, (C.label k).val ∈ supports i) : False := by
  classical
  by_cases hsingle : Subsingleton Q
  · let i : Fin C.length := ⟨0,by have := C.hlength; omega⟩
    let j : Fin C.length := ⟨1,by have := C.hlength; omega⟩
    obtain ⟨u,hu⟩ := hcover i
    obtain ⟨w,hw⟩ := hcover j
    have he : u = w := hsingle.allEq _ _
    subst w
    have hl := hmark u _ _ hu hw (C.label i).property (C.label j).property
    have hij := C.label_injective (Subtype.ext hl)
    have hv := congrArg Fin.val hij
    change (0 : ℕ) = 1 at hv
    omega
  · letI : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hsingle
    obtain ⟨leaf,parent,hadj,huniq,_⟩ := J.exists_leaf_attachment
    let K := {i : Q // i ∈ ({leaf} : Set Q)ᶜ}
    by_cases hkeep : ∀ k, ∃ i : K, (C.label k).val ∈ supports i.val
    · letI : Fintype K := Fintype.ofFinite K
      let J' := J.eraseLeaf hadj huniq
      exact contact_marked_cycle_impossible (Q := K) (fun i : K => carrier i.val) edge
        (fun i : K => supports i.val) marked J'
        (fun i e he => hsub i.val e he)
        (fun i e f he hf hme hmf => hmark i.val e f he hf hme hmf)
        hlin
        (fun i j hn => hsep i.val j.val (fun he => hn (Subtype.ext he)))
        C hkeep
    · push_neg at hkeep
      obtain ⟨k,hk⟩ := hkeep
      obtain ⟨i,hi⟩ := hcover k
      have hil : i = leaf := by
        by_contra hn
        exact hk ⟨i,by simpa using hn⟩ hi
      subst i
      obtain ⟨prev,hp⟩ := contactSucc_surjective k
      have hpne : prev ≠ k := by
        intro he
        exact contactSucc_ne C.hlength prev (hp.trans he.symm)
      have hnne : cyclicSucc k ≠ k := contactSucc_ne C.hlength k
      have hother (l : Fin C.length) (hl : l ≠ k) :
          ∃ j : Q, j ≠ leaf ∧ (C.label l).val ∈ supports j := by
        obtain ⟨j,hj⟩ := hcover l
        refine ⟨j,?_,hj⟩
        intro he
        subst j
        exact hl (C.label_injective (Subtype.ext
          (hmark leaf _ _ hj hi (C.label l).property (C.label k).property)))
      obtain ⟨left,hleft,hL⟩ := hother prev hpne
      obtain ⟨right,hright,hR⟩ := hother (cyclicSucc k) hnne
      have hx : C.vertex k ∈ edge (C.label k).val := C.left_mem k
      have hy : C.vertex prev ∈ edge (C.label k).val := by
        have hy := C.right_mem prev
        rw [hp] at hy
        exact hy
      have hxP := J.mem_parent_of_mem_leaf_and_other hadj huniq hright
        (hsub leaf _ hi hx) (hsub right _ hR (C.right_mem k))
      have hyP := J.mem_parent_of_mem_leaf_and_other hadj huniq hleft
        (hsub leaf _ hi hy) (hsub left _ hL (C.left_mem prev))
      have hxy : C.vertex prev ≠ C.vertex k := fun h => hpne (C.vertex_injective h)
      have hxp : C.vertex k ∈ carrier leaf ∩ carrier parent :=
        ⟨hsub leaf _ hi hx,hxP⟩
      have hyp : C.vertex prev ∈ carrier leaf ∩ carrier parent :=
        ⟨hsub leaf _ hi hy,hyP⟩
      rcases hsep leaf parent hadj.ne with hsmall | ⟨e,heL,heP,he⟩
      · exact hxy (hsmall hyp hxp)
      · rw [he] at hxp hyp
        have heq : (C.label k).val = e := by
          by_contra hn
          exact hxy (hlin _ _ hn ⟨hy,hyp⟩ ⟨hx,hxp⟩)
        exact hk ⟨parent,by simpa using hadj.ne.symm⟩ (heq.symm ▸ heP)
termination_by Nat.card Q
decreasing_by
  classical
  letI : Fintype K := Fintype.ofFinite K
  simp only [Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_not_surjective
    (fun i : K => i.val) Subtype.val_injective
  intro hsurj
  obtain ⟨i,hi⟩ := hsurj leaf
  have hn : i.val ∉ ({leaf} : Set Q) := i.property
  exact hn (Set.mem_singleton_iff.mpr hi)

end StructuralRamsey.Girth

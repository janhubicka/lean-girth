import Girth.ContactCompletionSharpness

/-! Irreducible substructures of the pure cycle are contained in
one of its actual two-point edge carriers. This supplies the
irreducible-cover clause of the vertex-cutoff sharpness example. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

private theorem contactPureCycle_no_triangle {n : ℕ} (hn : 4 ≤ n)
    (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h1 : cyclicSucc i = j ∨ cyclicSucc j = i)
    (h2 : cyclicSucc i = k ∨ cyclicSucc k = i)
    (h3 : cyclicSucc j = k ∨ cyclicSucc k = j) : False := by
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  have hne1 : i.val ≠ j.val := fun he => hij (Fin.ext he)
  have hne2 : i.val ≠ k.val := fun he => hik (Fin.ext he)
  have hne3 : j.val ≠ k.val := fun he => hjk (Fin.ext he)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    have a := congrArg Fin.val h1 <;>
    have b := congrArg Fin.val h2 <;>
    have c := congrArg Fin.val h3 <;>
    rw [contactSucc_value] at a b c <;>
    split_ifs at a b c <;> omega

/-- In a pure cycle of length at least four, every irreducible
induced substructure is contained in one actual cycle edge. The
empty and singleton substructures are included. -/
theorem contactSharpPureCycle_irreducible_edge {n : ℕ} (hn : 4 ≤ n)
    (S : Set (Fin n)) (hS : ((contactSharpPureCycle n).induce S).Irreducible) :
    ∃ e : Fin n, S ⊆ contactCycleEdge n e := by
  classical
  have hclique (x : Fin n) (hx : x ∈ S) (y : Fin n) (hy : y ∈ S) (hxy : x ≠ y) :
      cyclicSucc x = y ∨ cyclicSucc y = x := by
    have hne : (⟨x,hx⟩ : S) ≠ ⟨y,hy⟩ :=
      fun he => hxy (congrArg Subtype.val he)
    obtain ⟨R,t,i,j,hr,hi,hj⟩ := hS hne
    cases R with
    | inl R => exact Empty.elim R
    | inr _ =>
      change Fin 2 → S at t
      change Fin 2 at i j
      change (t 0).val < (t 1).val ∧
        (cyclicSucc (t 0).val = (t 1).val ∨ cyclicSucc (t 1).val = (t 0).val) at hr
      have hvi : (t i).val = x := congrArg Subtype.val hi
      have hvj : (t j).val = y := congrArg Subtype.val hj
      fin_cases i <;> fin_cases j
      · exact (hxy (hvi.symm.trans hvj)).elim
      · rw [← hvi,← hvj]
        exact hr.2
      · rw [← hvi,← hvj]
        exact hr.2.symm
      · exact (hxy (hvi.symm.trans hvj)).elim
  by_cases hsub : S.Subsingleton
  · by_cases hne : S.Nonempty
    · obtain ⟨x,hx⟩ := hne
      refine ⟨x,?_⟩
      intro y hy
      rw [hsub hy hx]
      exact Set.mem_insert _ _
    · exact ⟨⟨0,by omega⟩,fun _ hx => (hne ⟨_,hx⟩).elim⟩
  · obtain ⟨x,hx,y,hy,hxy⟩ := Set.not_subsingleton_iff.mp hsub
    have hxy' := hclique x hx y hy hxy
    obtain ⟨e,hxe,hye⟩ := (contactCycleEdge_pair_iff hxy).mpr hxy'
    refine ⟨e,?_⟩
    intro z hz
    by_cases hzx : z = x
    · exact hzx.symm ▸ hxe
    by_cases hzy : z = y
    · exact hzy.symm ▸ hye
    have hxz : x ≠ z := fun he => hzx he.symm
    have hyz : y ≠ z := fun he => hzy he.symm
    exact (contactPureCycle_no_triangle hn x y z hxy hxz hyz
      hxy' (hclique x hx z hz hxz) (hclique y hy z hz hyz)).elim

end StructuralRamsey.Girth

import Girth.CyclicRun
import Girth.BergePath
import Girth.BergeSegment

/-! # Berge girth under elementary hypergraph gluings

These lemmas isolate the pure incidence argument behind the girth clause of
supported tree amalgams.  Relational localization is handled elsewhere.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- Gluing two hypergraphs through a subsingleton vertex set preserves every
Berge-girth lower bound, provided every cross-side edge intersection is
contained in that separator. -/
theorem girthGT_union_of_subsingleton_glue
    {HL HR : Set (Set W)} {S : Set W} {g : ℕ}
    (hS : S.Subsingleton)
    (hcross : ∀ ⦃eL eR : Set W⦄, eL ∈ HL → eR ∈ HR →
      eL ∩ eR ⊆ S)
    (hL : GirthGT HL g) (hR : GirthGT HR g) :
    GirthGT (HL ∪ HR) g := by
  rintro ⟨c, hc⟩
  classical
  by_cases hallR : ∀ i, c.edge i ∈ HR
  · exact hR ⟨c.ofEdgeMem hallR, hc⟩
  by_cases hallL : ∀ i, c.edge i ∈ HL
  · exact hL ⟨c.ofEdgeMem hallL, hc⟩
  push_neg at hallR hallL
  let side : Fin c.length → Bool :=
    fun i => decide (c.edge i ∈ HR)
  have hR_of_true {i : Fin c.length} (hi : side i = true) :
      c.edge i ∈ HR := by
    exact of_decide_eq_true (by simpa [side] using hi)
  have hnotR_of_false {i : Fin c.length} (hi : side i = false) :
      c.edge i ∉ HR := by
    exact of_decide_eq_false (by simpa [side] using hi)
  have hL_of_false {i : Fin c.length} (hi : side i = false) :
      c.edge i ∈ HL := by
    rcases c.edge_mem i with hli | hri
    · exact hli
    · exact (hnotR_of_false hi hri).elim
  obtain ⟨iR, hiR⟩ := hallR
  obtain ⟨iL, hiL⟩ := hallL
  have hiSide : side iR = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hiR (hR_of_true h)
  have hiLR : c.edge iL ∈ HR := by
    rcases c.edge_mem iL with hli | hri
    · exact (hiL hli).elim
    · exact hri
  have hjSide : side iL = true := by
    apply Bool.eq_true_of_not_eq_false
    intro h
    exact hnotR_of_false h hiLR
  have hmix : ∃ i j : Fin c.length, side i ≠ side j :=
    ⟨iR, iL, by simp [hiSide, hjSide]⟩
  obtain ⟨i, j, hij, hi, hj⟩ :=
    exists_two_cyclic_changes c.hlength side hmix
  have transition_mem (q : Fin c.length)
      (hq : side q ≠ side (cyclicSucc q)) :
      c.vertex q ∈ S := by
    cases hq0 : side q <;>
      cases hq1 : side (cyclicSucc q)
    · exact (hq (by simp [hq0, hq1])).elim
    ·
      have hqL := hL_of_false hq0
      have hnextR := hR_of_true hq1
      exact hcross hqL hnextR ⟨c.left_mem q, c.right_mem q⟩
    ·
      have hqR := hR_of_true hq0
      have hnextL := hL_of_false hq1
      exact hcross hnextL hqR ⟨c.right_mem q, c.left_mem q⟩
    · exact (hq (by simp [hq0, hq1])).elim
  have hvi : c.vertex i ∈ S := transition_mem i hi
  have hvj : c.vertex j ∈ S := transition_mem j hj
  exact hij (c.vertex_injective (hS hvi hvj))

end StructuralRamsey.Girth

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
  push Not at hallR hallL
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
  obtain ⟨iFalse, hiNotR⟩ := hallR
  obtain ⟨iNotL, hiNotL⟩ := hallL
  have hiFalse : side iFalse = false := by
    simp [side, hiNotR]
  have hiTrue : side iNotL = true := by
    apply Bool.eq_true_of_not_eq_false
    intro hf
    exact hiNotL (hL_of_false hf)
  have hmix : ∃ i j : Fin c.length, side i ≠ side j :=
    ⟨iFalse, iNotL, by simp [hiFalse, hiTrue]⟩
  obtain ⟨before, k, hkpos, hbeforeTrue, hstartFalse,
    _hrun, hlastFalse, hnextTrue⟩ :=
    exists_false_cyclic_run c.hlength side hmix
  let lastIndex : Fin c.length := before + k
  have hbeforeChange :
      side before ≠ side (cyclicSucc before) := by
    rw [hbeforeTrue, hstartFalse]
    decide
  have hlastChange :
      side lastIndex ≠ side (cyclicSucc lastIndex) := by
    dsimp [lastIndex]
    rw [hlastFalse, hnextTrue]
    decide
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
  have hvi : c.vertex before ∈ S :=
    transition_mem before hbeforeChange
  have hvj : c.vertex lastIndex ∈ S :=
    transition_mem lastIndex hlastChange
  have hidx : before ≠ lastIndex := by
    intro hEq
    let z : Fin c.length := ⟨0, by omega⟩
    have hzadd : before + z = before := by
      apply Fin.ext
      simp [z, Fin.add_def]
    have hkzero : k = z := by
      apply add_left_cancel (a := before)
      calc
        before + k = before := by simpa [lastIndex] using hEq.symm
        _ = before + z := hzadd.symm
    have hv := congrArg Fin.val hkzero
    change k.1 = 0 at hv
    exact hkpos.ne' hv
  exact hidx (c.vertex_injective (hS hvi hvj))


/-- Gluing two hypergraphs along a common separator edge preserves Berge
girth, provided every cross-side edge intersection is contained in the
separator. -/
theorem girthGT_union_of_edge_glue
    {HL HR : Set (Set W)} {separator : Set W} {g : ℕ}
    (hsepL : separator ∈ HL) (hsepR : separator ∈ HR)
    (hcross : ∀ ⦃eL eR : Set W⦄, eL ∈ HL → eR ∈ HR →
      eL ∩ eR ⊆ separator)
    (hL : GirthGT HL g) (hR : GirthGT HR g) :
    GirthGT (HL ∪ HR) g := by
  rintro ⟨c, hcLen⟩
  classical
  by_cases hallR : ∀ i, c.edge i ∈ HR
  · exact hR ⟨c.ofEdgeMem hallR, hcLen⟩
  push Not at hallR
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
  obtain ⟨iFalse, hiNotR⟩ := hallR
  have hiFalse : side iFalse = false := by
    simp [side, hiNotR]
  by_cases hTrue : ∃ i : Fin c.length, side i = true
  · obtain ⟨iTrue, hiTrue⟩ := hTrue
    have hmix : ∃ i j : Fin c.length, side i ≠ side j :=
      ⟨iFalse, iTrue, by simp [hiFalse, hiTrue]⟩
    obtain ⟨before, k, hkpos, hbeforeTrue, hstartFalse,
      hrun, hlastFalse, hnextTrue⟩ :=
      exists_false_cyclic_run c.hlength side hmix
    let pU : BergePath (HL ∪ HR) :=
      c.cyclicPath before k.1 hkpos k.2
    have pEdgesL : ∀ t, pU.edge t ∈ HL := by
      intro t
      let m : Fin c.length :=
        Fin.castLE (Nat.le_of_lt k.2) t
      have hm : m < k := by
        rw [Fin.lt_def]
        exact t.2
      have hs : side (cyclicRunIndex before m) = false :=
        hrun m hm
      have hmem := hL_of_false hs
      change (c.cyclicPath before k.1 hkpos k.2).edge t ∈ HL
      rw [c.cyclicPath_edge before k.1 hkpos k.2 t]
      simpa [m] using hmem
    let pL : BergePath HL := pU.ofEdgeMem pEdgesL
    have hstartSep : c.vertex before ∈ separator := by
      have hRbefore := hR_of_true hbeforeTrue
      have hLnext := hL_of_false hstartFalse
      exact hcross hLnext hRbefore
        ⟨c.right_mem before, c.left_mem before⟩
    let lastIndex : Fin c.length := before + k
    have hendSep : c.vertex lastIndex ∈ separator := by
      have hLlast := hL_of_false hlastFalse
      have hRnext := hR_of_true hnextTrue
      exact hcross hLlast hRnext
        ⟨c.left_mem lastIndex, c.right_mem lastIndex⟩
    have hpStart : pL.vertex 0 ∈ separator := by
      change pU.vertex 0 ∈ separator
      simpa [pU] using hstartSep
    have hpEnd : pL.vertex (Fin.last k.1) ∈ separator := by
      change pU.vertex (Fin.last k.1) ∈ separator
      have hEndEq :
          pU.vertex (Fin.last k.1) = c.vertex lastIndex := by
        simpa [pU, lastIndex] using
          c.cyclicPath_vertex_last before k.1 hkpos k.2
      rw [hEndEq]
      exact hendSep
    have hpNew : ∀ t, pL.edge t ≠ separator := by
      intro t hEq
      let m : Fin c.length :=
        Fin.castLE (Nat.le_of_lt k.2) t
      have hm : m < k := by
        rw [Fin.lt_def]
        exact t.2
      have hs : side (cyclicRunIndex before m) = false :=
        hrun m hm
      have hnotR := hnotR_of_false hs
      apply hnotR
      have hEdge :
          pL.edge t =
            c.edge (cyclicRunIndex before m) := by
        change pU.edge t =
          c.edge (cyclicRunIndex before m)
        simpa [pU, m] using
          c.cyclicPath_edge before k.1 hkpos k.2 t
      rw [← hEdge, hEq]
      exact hsepR
    let closed : BergeCycle HL :=
      pL.close separator hsepL hpNew hpStart hpEnd
    have hClosedLen : closed.length ≤ g := by
      change k.1 + 1 ≤ g
      omega
    exact hL ⟨closed, hClosedLen⟩
  · have hallFalse : ∀ i : Fin c.length, side i = false := by
      intro i
      cases hi : side i
      · rfl
      · exact (hTrue ⟨i, hi⟩).elim
    have hallL : ∀ i, c.edge i ∈ HL :=
      fun i => hL_of_false (hallFalse i)
    exact hL ⟨c.ofEdgeMem hallL, hcLen⟩

end StructuralRamsey.Girth

import Girth.BergeSegment
import Mathlib.Tactic

/-!
# The exact girth test for a genuinely fresh support edge

A short Berge cycle created by inserting one fresh edge is equivalent
to an old Berge path joining two vertices of that edge. This is a
pure incidence statement; it does not claim a successor-history normal
form or preservation of designated B-copy forests.
-/

namespace StructuralRamsey.Girth

universe v

/-- An old Berge path which can be closed by a proposed new edge to
give a cycle with at most `m` edges. The endpoints are automatically
distinct because Berge paths have injective vertex enumerations. -/
def HasShortBergePathThrough {W : Type v}
    (E : Set (Set W)) (e : Set W) (m : ℕ) : Prop :=
  ∃ p : BergePath E, p.length + 1 ≤ m ∧
    p.vertex 0 ∈ e ∧ p.vertex (Fin.last p.length) ∈ e

/-- Cutting a short cycle at its new edge gives an old Berge path;
conversely every such path can be closed using the new edge. -/
theorem girthGT_insert_iff_noShortBergePath
    {W : Type v} (E : Set (Set W)) (e : Set W) (m : ℕ)
    (hNew : e ∉ E) :
    GirthGT (insert e E) m ↔
      GirthGT E m ∧ ¬ HasShortBergePathThrough E e m := by
  classical
  constructor
  · intro hGirth
    have hOld : GirthGT E m :=
      girthGT_of_subset (fun a ha => Set.mem_insert_of_mem e ha) hGirth
    refine ⟨hOld, ?_⟩
    rintro ⟨p, hpLen, hpStart, hpEnd⟩
    let pNew : BergePath (insert e E) :=
      p.ofEdgeMem (fun i => Set.mem_insert_of_mem e (p.edge_mem i))
    have hpDistinct : ∀ i, pNew.edge i ≠ e := by
      intro i hi
      apply hNew
      have hpMem := p.edge_mem i
      change p.edge i = e at hi
      exact hi ▸ hpMem
    let c : BergeCycle (insert e E) :=
      pNew.close e (Set.mem_insert e E) hpDistinct hpStart hpEnd
    exact hGirth ⟨c, hpLen⟩
  · rintro ⟨hOld, hNoPath⟩
    rintro ⟨c, hcLen⟩
    by_cases hHit : ∃ i : Fin c.length, c.edge i = e
    · obtain ⟨before, hBefore⟩ := hHit
      let k := c.length - 1
      have hkPos : 0 < k := by
        dsimp [k]
        omega
      have hkLt : k < c.length := by
        dsimp [k]
        omega
      let pFull : BergePath (insert e E) :=
        c.cyclicPath before k hkPos hkLt
      have hEdges (i : Fin k) : pFull.edge i ∈ E := by
        let off : Fin c.length :=
          Fin.castLE (Nat.le_of_lt hkLt) i
        have hProper : off.val + 1 < c.length := by
          change i.val + 1 < c.length
          omega
        have hDifferent : c.edge (cyclicRunIndex before off) ≠ e := by
          intro hEq
          have hSame : cyclicRunIndex before off = before :=
            c.edge_injective (hEq.trans hBefore.symm)
          exact cyclicRunIndex_ne_before before off hProper hSame
        have hMem : c.edge (cyclicRunIndex before off) ∈ E := by
          rcases Set.mem_insert_iff.mp
              (c.edge_mem (cyclicRunIndex before off)) with hEq | hOldEdge
          · exact (hDifferent hEq).elim
          · exact hOldEdge
        change (c.cyclicPath before k hkPos hkLt).edge i ∈ E
        rw [c.cyclicPath_edge before k hkPos hkLt i]
        exact hMem
      have hStart : pFull.vertex 0 ∈ e := by
        rw [c.cyclicPath_vertex_zero before k hkPos hkLt]
        rw [← hBefore]
        exact c.left_mem before
      have hkZero :
          (⟨k, hkLt⟩ : Fin c.length) + 1 = 0 := by
        apply Fin.ext
        change (k + (1 % c.length)) % c.length = 0
        rw [Nat.mod_eq_of_lt (by omega : 1 < c.length)]
        have hkVal : k + 1 = c.length := by
          dsimp [k]
          omega
        rw [hkVal]
        simp
      have hWrap :
          cyclicSucc (before + (⟨k, hkLt⟩ : Fin c.length)) =
            before := by
        rw [cyclicSucc_eq_finRotate, finRotate_apply]
        calc
          before + (⟨k, hkLt⟩ : Fin c.length) + 1 =
              before + ((⟨k, hkLt⟩ : Fin c.length) + 1) := by ac_rfl
          _ = before + 0 := by rw [hkZero]
          _ = before := by simp
      have hEnd : pFull.vertex (Fin.last k) ∈ e := by
        rw [c.cyclicPath_vertex_last before k hkPos hkLt]
        have hConn := c.right_mem
          (before + (⟨k, hkLt⟩ : Fin c.length))
        rw [hWrap, hBefore] at hConn
        exact hConn
      let p : BergePath E := pFull.ofEdgeMem hEdges
      have hLen : p.length + 1 ≤ m := by
        change k + 1 ≤ m
        dsimp [k]
        omega
      exact hNoPath ⟨p, hLen, hStart, hEnd⟩
    · have hEdges : ∀ i, c.edge i ∈ E := by
        intro i
        rcases Set.mem_insert_iff.mp (c.edge_mem i) with hEq | hMem
        · exact (hHit ⟨i, hEq⟩).elim
        · exact hMem
      exact hOld ⟨c.ofEdgeMem hEdges, hcLen⟩

end StructuralRamsey.Girth

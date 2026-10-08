import Girth.BergeSegment
import Mathlib.Tactic

/-!
# Exact one-edge extension criterion for Berge girth

A new edge creates a short Berge cycle precisely when the old hypergraph
already has a short Berge path joining two different vertices of that edge.
The path must use distinct old edges and distinct connector vertices; it is
not an induced path.  This is the boundary condition needed in the successor
history construction, independently of the later B-owner forest data.
-/

namespace StructuralRamsey.Girth

universe v

/-- An old nonempty Berge path shorter than g, with both endpoints on the
proposed new edge. Injectivity of path vertices makes the endpoints distinct. -/
def HasShortBergePathToEdge {W : Type v}
    (H : Set (Set W)) (e : Set W) (g : ℕ) : Prop :=
  ∃ p : BergePath H, p.length < g ∧
    p.vertex 0 ∈ e ∧ p.vertex (Fin.last p.length) ∈ e

/-- Any old short path between two points of the fresh edge closes to a
short cycle in the augmented hypergraph. -/
theorem no_shortBergePath_of_girthGT_insert
    {W : Type v} (H : Set (Set W)) (e : Set W) (g : ℕ)
    (hnew : e ∉ H) (hgt : GirthGT (insert e H) g) :
    ¬ HasShortBergePathToEdge H e g := by
  rintro ⟨p, hlen, hstart, hend⟩
  let q : BergePath (insert e H) :=
    p.ofEdgeMem (fun i => Set.mem_insert_of_mem e (p.edge_mem i))
  have hne : ∀ i, q.edge i ≠ e := by
    intro i hi
    exact hnew (hi ▸ p.edge_mem i)
  let c : BergeCycle (insert e H) :=
    q.close e (Set.mem_insert e H) hne hstart hend
  apply hgt
  refine ⟨c, ?_⟩
  change p.length + 1 ≤ g
  omega

/-- Extracting the rest of a cycle after its unique new edge, or closing a
short old path, gives the exact girth-preservation criterion.  The
freshness hypothesis is essential: a path using e itself would not give
a cycle with distinct edges. -/
theorem girthGT_insert_iff_no_shortBergePath
    {W : Type v} (H : Set (Set W)) (e : Set W) (g : ℕ)
    (hnew : e ∉ H) :
    GirthGT (insert e H) g ↔
      GirthGT H g ∧ ¬ HasShortBergePathToEdge H e g := by
  constructor
  · intro hgt
    exact ⟨girthGT_of_subset
      (fun a ha => Set.mem_insert_of_mem e ha) hgt,
      no_shortBergePath_of_girthGT_insert H e g hnew hgt⟩
  · rintro ⟨hold, hno⟩ ⟨c, hlen⟩
    classical
    by_cases hfresh : ∃ j : Fin c.length, c.edge j = e
    · obtain ⟨j, hj⟩ := hfresh
      let k : ℕ := c.length - 1
      have hkpos : 0 < k := by
        dsimp [k]
        omega
      have hklt : k < c.length := by
        dsimp [k]
        omega
      let q : BergePath (insert e H) :=
        c.cyclicPath j k hkpos hklt
      have hOldEdges : ∀ i, q.edge i ∈ H := by
        intro i
        let off : Fin c.length := Fin.castLE (Nat.le_of_lt hklt) i
        have hproper : off.val + 1 < c.length := by
          change i.val + 1 < c.length
          have hi := i.isLt
          dsimp [k] at hi
          omega
        have hidx : cyclicRunIndex j off ≠ j :=
          cyclicRunIndex_ne_before j off hproper
        have hmem : c.edge (cyclicRunIndex j off) ∈ H := by
          rcases Set.mem_insert_iff.mp (c.edge_mem (cyclicRunIndex j off)) with he | he
          · exfalso
            apply hidx
            exact c.edge_injective (he.trans hj.symm)
          · exact he
        simpa only [q, BergeCycle.cyclicPath_edge] using hmem
      let p : BergePath H := q.ofEdgeMem hOldEdges
      apply hno
      refine ⟨p, ?_, ?_, ?_⟩
      · change k < g
        dsimp [k]
        omega
      · change (c.cyclicPath j k hkpos hklt).vertex 0 ∈ e
        rw [BergeCycle.cyclicPath_vertex_zero]
        simpa only [hj] using c.left_mem j
      · change (c.cyclicPath j k hkpos hklt).vertex (Fin.last k) ∈ e
        rw [BergeCycle.cyclicPath_vertex_last]
        have hOffset : ((⟨k, hklt⟩ : Fin c.length) + 1) = 0 := by
          apply Fin.ext
          change (k + 1 % c.length) % c.length = 0
          rw [Nat.mod_eq_of_lt (show 1 < c.length by omega)]
          rw [show k + 1 = c.length by dsimp [k]; omega]
          exact Nat.mod_self _
        have hSucc :
            cyclicSucc (j + (⟨k, hklt⟩ : Fin c.length)) = j := by
          calc
            cyclicSucc (j + (⟨k, hklt⟩ : Fin c.length)) =
                finRotate c.length (j + (⟨k, hklt⟩ : Fin c.length)) :=
              cyclicSucc_eq_finRotate _
            _ = j + (⟨k, hklt⟩ : Fin c.length) + 1 := by
              rw [finRotate_apply]
            _ = j + ((⟨k, hklt⟩ : Fin c.length) + 1) := by ac_rfl
            _ = j := by rw [hOffset]; simp
        rw [← hj, ← hSucc]
        exact c.right_mem (j + (⟨k, hklt⟩ : Fin c.length))
    · have hOldEdges : ∀ i, c.edge i ∈ H := by
        intro i
        rcases Set.mem_insert_iff.mp (c.edge_mem i) with he | he
        · exact (hfresh ⟨i, he⟩).elim
        · exact he
      exact hold ⟨c.ofEdgeMem hOldEdges, hlen⟩

end StructuralRamsey.Girth

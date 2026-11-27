import Girth.ContactGraph
import Mathlib.Data.Fin.Tuple.Basic

/-! The abstract part of Observation obs:triangulation.
The reverse implication is unconditional. The forward implication is
proved from the explicit polygon-cut interface below, whose construction
for all chords remains a separate obligation. No equivalence is assumed
in the definition of system girth. -/

namespace StructuralRamsey.Girth
universe v
variable {V P J : Type v}
variable {K : J → Set (V ⊕ P)}

namespace ContactPolygon

variable (C : ContactPolygon V P)

theorem shared_hasChord (h : C.HasSharedChord K) : C.HasChord K := by
  obtain ⟨i,j,hnc,a,b,hab,hia,hja,hib,hjb⟩ := h
  exact ⟨i,j,hnc,fun he => hnc.1 (C.vertex_injective he),a,hia,hja⟩

theorem covered_hasChord (hlen : 4 ≤ C.length) (h : C.Covered K) :
    C.HasChord K := by
  obtain ⟨a,ha⟩ := h
  let i : Fin C.length := ⟨0, by omega⟩
  let j : Fin C.length := ⟨2, by omega⟩
  have hij : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change (0 : ℕ) = 2 at hv
    omega
  have hsucc : cyclicSucc i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change (0+1) % C.length = 2 at hv
    rw [Nat.mod_eq_of_lt (show 0+1 < C.length by omega)] at hv
    omega
  have hpred : cyclicSucc j ≠ i := by
    intro he
    have hv := congrArg Fin.val he
    change (2+1) % C.length = 0 at hv
    rw [Nat.mod_eq_of_lt (show 2+1 < C.length by omega)] at hv
    omega
  exact ⟨i,j,⟨hij,hsucc,hpred⟩,fun he => hij (C.vertex_injective he),a,ha i,ha j⟩

private theorem triangle_no_nonconsecutive {n : ℕ} (hn : n = 3)
    (i j : Fin n) (hne : i ≠ j)
    (hi : cyclicSucc i ≠ j) (hj : cyclicSucc j ≠ i) : False := by
  subst n
  fin_cases i <;> fin_cases j <;> simp_all [cyclicSucc]

theorem triangle_not_shared (hlen : C.length = 3) : ¬ C.HasSharedChord K := by
  rintro ⟨i,j,hnc,_⟩
  exact triangle_no_nonconsecutive hlen i j hnc.1 hnc.2.1 hnc.2.2

/-- Data of an actual cut along a chord. No shared-clique conclusion is
assumed. The remaining construction must supply the two cyclic intervals,
their side weights, and the indicated vertex maps. -/
structure Split (C : ContactPolygon V P) (K : J → Set (V ⊕ P)) where
  left : ContactPolygon V P
  right : ContactPolygon V P
  leftMap : Fin left.length → Fin C.length
  rightMap : Fin right.length → Fin C.length
  left_vertex : ∀ i, left.vertex i = C.vertex (leftMap i)
  right_vertex : ∀ i, right.vertex i = C.vertex (rightMap i)
  left_cycle : left.IsCycle K
  right_cycle : right.IsCycle K
  left_weight : left.twiceWeight ≤ C.twiceWeight
  right_weight : right.twiceWeight ≤ C.twiceWeight
  left_smaller : left.length < C.length
  right_smaller : right.length < C.length
  left_nonc : ∀ i j, left.Nonconsecutive i j →
    C.Nonconsecutive (leftMap i) (leftMap j)
  right_nonc : ∀ i j, right.Nonconsecutive i j →
    C.Nonconsecutive (rightMap i) (rightMap j)
  cover : ∀ i : Fin C.length, i ∈ Set.range leftMap ∨ i ∈ Set.range rightMap
  side_cover : ∀ i : Fin C.length,
    (∃ a : Fin left.length, leftMap a = i ∧
      leftMap (cyclicSucc a) = cyclicSucc i) ∨
    (∃ a : Fin right.length, rightMap a = i ∧
      rightMap (cyclicSucc a) = cyclicSucc i)
  chord : ∃ i j, C.Nonconsecutive i j ∧
    i ∈ Set.range leftMap ∧ j ∈ Set.range leftMap ∧
    i ∈ Set.range rightMap ∧ j ∈ Set.range rightMap

namespace Split
variable {C : ContactPolygon V P} (S : C.Split K)

theorem lift_left (h : S.left.HasSharedChord K) : C.HasSharedChord K := by
  obtain ⟨i,j,hnc,a,b,hab,hia,hja,hib,hjb⟩ := h
  refine ⟨S.leftMap i,S.leftMap j,S.left_nonc i j hnc,a,b,hab,?_,?_,?_,?_⟩
  · rw [← S.left_vertex i]; exact hia
  · rw [← S.left_vertex j]; exact hja
  · rw [← S.left_vertex i]; exact hib
  · rw [← S.left_vertex j]; exact hjb

theorem lift_right (h : S.right.HasSharedChord K) : C.HasSharedChord K := by
  obtain ⟨i,j,hnc,a,b,hab,hia,hja,hib,hjb⟩ := h
  refine ⟨S.rightMap i,S.rightMap j,S.right_nonc i j hnc,a,b,hab,?_,?_,?_,?_⟩
  · rw [← S.right_vertex i]; exact hia
  · rw [← S.right_vertex j]; exact hja
  · rw [← S.right_vertex i]; exact hib
  · rw [← S.right_vertex j]; exact hjb

theorem left_mem {a : J} (ha : ∀ i, S.left.vertex i ∈ K a)
    {k : Fin C.length} (hk : k ∈ Set.range S.leftMap) : C.vertex k ∈ K a := by
  obtain ⟨i,rfl⟩ := hk
  rw [← S.left_vertex i]
  exact ha i

theorem right_mem {a : J} (ha : ∀ i, S.right.vertex i ∈ K a)
    {k : Fin C.length} (hk : k ∈ Set.range S.rightMap) : C.vertex k ∈ K a := by
  obtain ⟨i,rfl⟩ := hk
  rw [← S.right_vertex i]
  exact ha i

/-- The triangulation-dual-tree argument reduces to this elementary
two-child operation. -/
theorem join_alternatives
    (hL : S.left.Covered K ∨ S.left.HasSharedChord K)
    (hR : S.right.Covered K ∨ S.right.HasSharedChord K) :
    C.Covered K ∨ C.HasSharedChord K := by
  classical
  rcases hL with ⟨a,ha⟩ | hs
  · rcases hR with ⟨b,hb⟩ | hs
    · by_cases hab : a = b
      · subst b
        left
        refine ⟨a,?_⟩
        intro k
        rcases S.cover k with hk | hk
        · exact S.left_mem ha hk
        · exact S.right_mem hb hk
      · right
        obtain ⟨i,j,hnc,hil,hjl,hir,hjr⟩ := S.chord
        exact ⟨i,j,hnc,a,b,hab,S.left_mem ha hil,S.left_mem ha hjl,
          S.right_mem hb hir,S.right_mem hb hjr⟩
    · exact Or.inr (S.lift_right hs)
  · exact Or.inr (S.lift_left hs)
end Split
end ContactPolygon

/-- The easy, unconditional direction of the shared-chord equivalence. -/
theorem contactG4_of_sharedChordBound {q : ℕ}
    (h : ContactSharedChordBound K q) : ContactG4 K q := by
  intro C hc hw
  rcases h C hc hw with hcover | hshared
  · exact ⟨fun _ => hcover, fun hn => C.covered_hasChord hn hcover⟩
  · exact ⟨fun hn => (C.triangle_not_shared hn hshared).elim,
      fun _ => C.shared_hasChord hshared⟩

/-- The forward proof is complete modulo the elementary polygon-cut
construction. The remaining hypothesis must be discharged, not cited
as a proof of the full manuscript observation. -/
theorem contactSharedChordBound_of_G4_of_splits {q : ℕ}
    (h : ContactG4 K q)
    (split : ∀ C : ContactPolygon V P, C.IsCycle K → C.HasChord K →
      Nonempty (C.Split K)) :
    ContactSharedChordBound K q := by
  have aux : ∀ n : ℕ, ∀ C : ContactPolygon V P, C.length = n →
      C.IsCycle K → C.twiceWeight ≤ 2*q →
      C.Covered K ∨ C.HasSharedChord K := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro C hlen hc hw
      by_cases htri : C.length = 3
      · exact Or.inl ((h C hc hw).1 htri)
      · have hfour : 4 ≤ C.length := by have := C.hlength; omega
        obtain ⟨S⟩ := split C hc ((h C hc hw).2 hfour)
        have hL : S.left.length < n := S.left_smaller.trans_le (by omega)
        have hR : S.right.length < n := S.right_smaller.trans_le (by omega)
        exact S.join_alternatives
          (ih S.left.length hL S.left rfl S.left_cycle (S.left_weight.trans hw))
          (ih S.right.length hR S.right rfl S.right_cycle (S.right_weight.trans hw))
  exact fun C hc hw => aux C.length C rfl hc hw

end StructuralRamsey.Girth

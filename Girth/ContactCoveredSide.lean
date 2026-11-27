import Girth.ContactPolygonSplit

/-! The covered-side part of the manuscript's short-cycle observation.
A designated side survives in one child of every chord split. -/

namespace StructuralRamsey.Girth

universe v
variable {V P J : Type v} {K : J → Set (V ⊕ P)}

private theorem third_index {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  by_cases h0 : i.val ≠ 0 ∧ j.val ≠ 0
  · exact ⟨⟨0,by omega⟩,fun he => h0.1 (congrArg Fin.val he).symm,
      fun he => h0.2 (congrArg Fin.val he).symm⟩
  by_cases h1 : i.val ≠ 1 ∧ j.val ≠ 1
  · exact ⟨⟨1,by omega⟩,fun he => h1.1 (congrArg Fin.val he).symm,
      fun he => h1.2 (congrArg Fin.val he).symm⟩
  have h2 : i.val ≠ 2 ∧ j.val ≠ 2 := by omega
  exact ⟨⟨2,by omega⟩,fun he => h2.1 (congrArg Fin.val he).symm,
    fun he => h2.2 (congrArg Fin.val he).symm⟩

namespace ContactPolygon

def HasCoveredSide (C : ContactPolygon V P) (K : J → Set (V ⊕ P))
    (k : Fin C.length) : Prop :=
  ∃ l : Fin C.length, l ≠ k ∧ l ≠ cyclicSucc k ∧
    ∃ a, C.vertex k ∈ K a ∧ C.vertex (cyclicSucc k) ∈ K a ∧
      C.vertex l ∈ K a

theorem covered_side_of_covered (C : ContactPolygon V P) (h : C.Covered K)
    (k : Fin C.length) : C.HasCoveredSide K k := by
  obtain ⟨l,hl,hl'⟩ := third_index C.hlength k (cyclicSucc k)
  obtain ⟨a,ha⟩ := h
  exact ⟨l,hl,hl',a,ha k,ha (cyclicSucc k),ha l⟩

/-- Transfer a covered side across any injective map of polygon vertices. -/
theorem covered_side_lift {C D : ContactPolygon V P}
    (f : Fin D.length → Fin C.length)
    (hf : ∀ i, D.vertex i = C.vertex (f i))
    {k : Fin C.length} {b : Fin D.length}
    (h0 : f b = k) (h1 : f (cyclicSucc b) = cyclicSucc k)
    (h : D.HasCoveredSide K b) : C.HasCoveredSide K k := by
  have hinj : Function.Injective f := by
    intro i j he
    apply D.vertex_injective
    rw [hf i,hf j,he]
  obtain ⟨l,hl,hl',a,hb,hb',hll⟩ := h
  refine ⟨f l,?_,?_,a,?_,?_,?_⟩
  · intro he
    exact hl (hinj (he.trans h0.symm))
  · intro he
    exact hl' (hinj (he.trans h1.symm))
  · rw [← h0,← hf b]
    exact hb
  · rw [← h1,← hf (cyclicSucc b)]
    exact hb'
  · rw [← hf l]
    exact hll

end ContactPolygon

/-- Every side of a short cycle is contained in a covered triangle on
the vertices of that cycle. This proves obs:triangulation(a), without
a triangulation data structure or an unproved splitting assumption. -/
theorem contactCoveredSide_of_G4 {q : ℕ} (h : ContactG4 K q)
    (C : ContactPolygon V P) (hc : C.IsCycle K) (hw : C.twiceWeight ≤ 2*q)
    (k : Fin C.length) : C.HasCoveredSide K k := by
  have aux : ∀ n : ℕ, ∀ C : ContactPolygon V P, C.length = n →
      C.IsCycle K → C.twiceWeight ≤ 2*q →
      ∀ k : Fin C.length, C.HasCoveredSide K k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro D hlen hd hweight b
      by_cases htri : D.length = 3
      · exact D.covered_side_of_covered ((h D hd hweight).1 htri) b
      · have hfour : 4 ≤ D.length := by have := D.hlength; omega
        obtain ⟨S⟩ := D.split_of_chord hd ((h D hd hweight).2 hfour)
        rcases S.side_cover b with ⟨a,ha,ha'⟩ | ⟨a,ha,ha'⟩
        · have hl : S.left.length < n := by have := S.left_smaller; omega
          exact ContactPolygon.covered_side_lift S.leftMap S.left_vertex ha ha'
            (ih S.left.length hl S.left rfl S.left_cycle (S.left_weight.trans hweight) a)
        · have hr : S.right.length < n := by have := S.right_smaller; omega
          exact ContactPolygon.covered_side_lift S.rightMap S.right_vertex ha ha'
            (ih S.right.length hr S.right rfl S.right_cycle (S.right_weight.trans hweight) a)
  exact aux C.length C rfl hc hw k

end StructuralRamsey.Girth

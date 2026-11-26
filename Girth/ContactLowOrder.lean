import Girth.ContactGraph
import Mathlib.Data.Fin.Tuple.Basic

/-! The low-order contact-graph cases used in Section 11.
They are consequences of the actual G4 predicate, not extra assumptions. -/

namespace StructuralRamsey.Girth
universe v
variable {V P J : Type v} {K : J → Set (V ⊕ P)}

theorem contactAdjacent_symm {x y : V ⊕ P}
    (h : contactAdjacent K x y) : contactAdjacent K y x := by
  obtain ⟨hne,j,hx,hy⟩ := h
  exact ⟨hne.symm,j,hy,hx⟩

/-- Any triangle of doubled weight at most four is covered under G4(2). -/
theorem contact_triangle_covered (h4 : ContactG4 K 2)
    (a b c : V ⊕ P)
    (hab : contactAdjacent K a b) (hbc : contactAdjacent K b c)
    (hca : contactAdjacent K c a)
    (hw : contactWeight a b + contactWeight b c + contactWeight c a ≤ 4) :
    ∃ j, a ∈ K j ∧ b ∈ K j ∧ c ∈ K j := by
  have hneAB := hab.1
  have hneBC := hbc.1
  have hneCA := hca.1
  let C : ContactPolygon V P := {
    length := 3
    hlength := by omega
    vertex := ![a,b,c]
    vertex_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  }
  have hc : C.IsCycle K := by
    intro i
    fin_cases i
    · simpa [C,cyclicSucc] using hab
    · simpa [C,cyclicSucc] using hbc
    · simpa [C,cyclicSucc] using hca
  have hweight : C.twiceWeight ≤ 2*2 := by
    simpa [ContactPolygon.twiceWeight,C,Fin.sum_univ_succ,cyclicSucc,
      Nat.add_assoc] using hw
  obtain ⟨j,hj⟩ := (h4 C hc hweight).1 rfl
  exact ⟨j,hj 0,hj 1,hj 2⟩

/-- Two real vertices and a wagon form a weight-two triangle. -/
theorem contact_vertex_wagon_vertex_covered (h4 : ContactG4 K 2)
    (x y : V) (p : P)
    (hxp : contactAdjacent K (Sum.inl x) (Sum.inr p))
    (hyp : contactAdjacent K (Sum.inl y) (Sum.inr p))
    (hxy : contactAdjacent K (Sum.inl x) (Sum.inl y)) :
    ∃ j, Sum.inl x ∈ K j ∧ Sum.inr p ∈ K j ∧ Sum.inl y ∈ K j := by
  apply contact_triangle_covered h4 _ _ _ hxp
    (contactAdjacent_symm hyp) (contactAdjacent_symm hxy)
  decide

/-- One real vertex and two wagons likewise form a weight-two triangle. -/
theorem contact_vertex_wagon_wagon_covered (h4 : ContactG4 K 2)
    (x : V) (p q : P)
    (hxp : contactAdjacent K (Sum.inl x) (Sum.inr p))
    (hxq : contactAdjacent K (Sum.inl x) (Sum.inr q))
    (hpq : contactAdjacent K (Sum.inr p) (Sum.inr q)) :
    ∃ j, Sum.inl x ∈ K j ∧ Sum.inr p ∈ K j ∧ Sum.inr q ∈ K j := by
  apply contact_triangle_covered h4 _ _ _ hxp hpq (contactAdjacent_symm hxq)
  decide

/-- The alternating quadrilateral is of weight two. Its only possible
chords are the real-vertex pair and the wagon pair. -/
theorem contact_alternating_quad_chord (h4 : ContactG4 K 2)
    (x y : V) (p q : P) (hxy : x ≠ y) (hpq : p ≠ q)
    (hxp : contactAdjacent K (Sum.inl x) (Sum.inr p))
    (hxq : contactAdjacent K (Sum.inl x) (Sum.inr q))
    (hyp : contactAdjacent K (Sum.inl y) (Sum.inr p))
    (hyq : contactAdjacent K (Sum.inl y) (Sum.inr q)) :
    contactAdjacent K (Sum.inl x) (Sum.inl y) ∨
      contactAdjacent K (Sum.inr p) (Sum.inr q) := by
  let C : ContactPolygon V P := {
    length := 4
    hlength := by omega
    vertex := ![Sum.inl x, Sum.inr p, Sum.inl y, Sum.inr q]
    vertex_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  }
  have hc : C.IsCycle K := by
    intro i
    fin_cases i
    · simpa [C,cyclicSucc] using hxp
    · simpa [C,cyclicSucc] using contactAdjacent_symm hyp
    · simpa [C,cyclicSucc] using hyq
    · simpa [C,cyclicSucc] using contactAdjacent_symm hxq
  have hw : C.twiceWeight ≤ 2*2 := by
    simp [ContactPolygon.twiceWeight,C,Fin.sum_univ_succ,cyclicSucc,
      contactWeight,contactKind,twiceOccurrenceWeight]
  obtain ⟨i,j,hnc,hadj⟩ := (h4 C hc hw).2 (by decide : 4 ≤ 4)
  fin_cases i <;> fin_cases j <;>
    simp [ContactPolygon.Nonconsecutive,cyclicSucc,C] at hnc hadj <;>
    first
    | exact Or.inl hadj
    | exact Or.inr hadj
    | exact Or.inl (contactAdjacent_symm hadj)
    | exact Or.inr (contactAdjacent_symm hadj)

namespace OrderOneData
variable {E I : Type v} (D : OrderOneData V E I P)

/-- The triangle with two wagon vertices is necessarily covered by a
designated clique, because a wagon clique contains only its own wagon. -/
theorem contact_two_wagon_triangle_in_copy
    (h4 : ContactG4 D.contactClique 2)
    (x : V) (p q : P) (hpq : p ≠ q)
    (hxp : contactAdjacent D.contactClique (Sum.inl x) (Sum.inr p))
    (hxq : contactAdjacent D.contactClique (Sum.inl x) (Sum.inr q))
    (hpqEdge : contactAdjacent D.contactClique (Sum.inr p) (Sum.inr q)) :
    ∃ i, x ∈ D.copyCarrier i ∧ D.contactMeets i p ∧ D.contactMeets i q := by
  obtain ⟨j,hx,hp,hq⟩ := contact_vertex_wagon_wagon_covered h4 x p q hxp hxq hpqEdge
  cases j with
  | inl i => exact ⟨i,hx,hp,hq⟩
  | inr w =>
    exact (hpq ((show p = w from hp).trans (show q = w from hq).symm)).elim

/-- The triangle with one wagon vertex is covered either by that wagon
or by a designated copy meeting it. -/
theorem contact_one_wagon_triangle
    (h4 : ContactG4 D.contactClique 2)
    (x y : V) (p : P)
    (hxp : contactAdjacent D.contactClique (Sum.inl x) (Sum.inr p))
    (hyp : contactAdjacent D.contactClique (Sum.inl y) (Sum.inr p))
    (hxy : contactAdjacent D.contactClique (Sum.inl x) (Sum.inl y)) :
    (x ∈ D.contactWagonCarrier p ∧ y ∈ D.contactWagonCarrier p) ∨
      ∃ i, x ∈ D.copyCarrier i ∧ y ∈ D.copyCarrier i ∧ D.contactMeets i p := by
  obtain ⟨j,hx,hp,hy⟩ := contact_vertex_wagon_vertex_covered h4 x y p hxp hyp hxy
  cases j with
  | inl i => exact Or.inr ⟨i,hx,hy,hp⟩
  | inr w =>
    have he : p = w := hp
    subst w
    exact Or.inl ⟨hx,hy⟩

end OrderOneData
end StructuralRamsey.Girth

import Girth.Berge
import Mathlib.Data.Fin.VecNotation

/-! # Cliques in high-girth linear hypergraphs

The structural local-forest corollary decorates each support edge by a copy of
the irreducible structure A.  To rule out unintended irreducible substructures,
we need the elementary fact that a clique in the two-section of a linear
hypergraph of Berge girth greater than three lies in one hyperedge.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- Every distinct pair of vertices in S is contained in a hyperedge. -/
def PairCoveredBy (H : Set (Set W)) (S : Set W) : Prop :=
  ∀ ⦃x y : W⦄, x ∈ S → y ∈ S → x ≠ y →
    ∃ e : Set W, e ∈ H ∧ x ∈ e ∧ y ∈ e

/-- Three pair-supporting edges arranged on three distinct vertices form a
Berge triangle. -/
theorem bergeTriangle_of_three_pair_edges
    {H : Set (Set W)}
    {x y z : W} (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    {eXY eYZ eZX : Set W}
    (hXY : eXY ∈ H) (hYZ : eYZ ∈ H) (hZX : eZX ∈ H)
    (hEdges : eXY ≠ eYZ ∧ eYZ ≠ eZX ∧ eZX ≠ eXY)
    (hxXY : x ∈ eXY) (hyXY : y ∈ eXY)
    (hyYZ : y ∈ eYZ) (hzYZ : z ∈ eYZ)
    (hzZX : z ∈ eZX) (hxZX : x ∈ eZX) :
    HasBergeCycleAtMost H 3 := by
  let c : BergeCycle H := {
    length := 3
    hlength := by omega
    edge := ![eXY, eYZ, eZX]
    vertex := ![y, z, x]
    edge_mem := by
      intro i
      fin_cases i
      · exact hXY
      · exact hYZ
      · exact hZX
    edge_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    vertex_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    left_mem := by
      intro i
      fin_cases i
      · exact hyXY
      · exact hzYZ
      · exact hxZX
    right_mem := by
      intro i
      fin_cases i
      · simpa [cyclicSucc] using hyYZ
      · simpa [cyclicSucc] using hzZX
      · simpa [cyclicSucc] using hxXY
  }
  exact ⟨c, by simp [c]⟩

/-- In Berge girth greater than three, three pair-supporting edges on a
triangle of vertices cannot all be distinct. -/
theorem three_pair_edges_not_all_distinct
    {H : Set (Set W)} (hgt : GirthGT H 3)
    {x y z : W} (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    {eXY eYZ eZX : Set W}
    (hXY : eXY ∈ H) (hYZ : eYZ ∈ H) (hZX : eZX ∈ H)
    (hxXY : x ∈ eXY) (hyXY : y ∈ eXY)
    (hyYZ : y ∈ eYZ) (hzYZ : z ∈ eYZ)
    (hzZX : z ∈ eZX) (hxZX : x ∈ eZX) :
    eXY = eYZ ∨ eYZ = eZX ∨ eZX = eXY := by
  by_contra h
  push_neg at h
  exact hgt (bergeTriangle_of_three_pair_edges
    hxy hyz hzx hXY hYZ hZX
    ⟨h.1, h.2.1, h.2.2⟩
    hxXY hyXY hyYZ hzYZ hzZX hxZX)

/-- If H has Berge girth greater than three, every nontrivial set whose
distinct pairs are covered by H is contained in one edge of H. -/
theorem pairCovered_subset_edge_of_girthGT_three
    {H : Set (Set W)} {S : Set W}
    (hgt : GirthGT H 3)
    (hS : S.Nontrivial)
    (hPair : PairCoveredBy H S) :
    ∃ e : Set W, e ∈ H ∧ S ⊆ e := by
  rcases hS with ⟨x, hx, y, hy, hxy⟩
  obtain ⟨eXY, heXY, hxXY, hyXY⟩ :=
    hPair hx hy hxy
  refine ⟨eXY, heXY, ?_⟩
  intro z hz
  by_cases hzx : z = x
  · simpa [hzx] using hxXY
  by_cases hzy : z = y
  · simpa [hzy] using hyXY
  obtain ⟨eYZ, heYZ, hyYZ, hzYZ⟩ :=
    hPair hy hz (Ne.symm hzy)
  obtain ⟨eZX, heZX, hzZX, hxZX⟩ :=
    hPair hz hx hzx
  rcases three_pair_edges_not_all_distinct hgt
      hxy (Ne.symm hzy) hzx
      heXY heYZ heZX
      hxXY hyXY hyYZ hzYZ hzZX hxZX with
    h1 | h2 | h3
  · rw [h1]
    exact hzYZ
  · have hlin : GirthGT H 2 :=
      girthGT_mono hgt (by omega)
    have hsmall :=
      pairwise_subsingleton_of_girthGT_two hlin
        heXY heYZ
    by_cases hEq : eXY = eYZ
    · rw [hEq]
      exact hzYZ
    · exfalso
      exact hxy (hsmall hEq
        ⟨hxXY, by rw [h2]; exact hxZX⟩
        ⟨hyXY, hyYZ⟩)
  · rw [← h3]
    exact hzZX



/-- Every relation tuple of R is supported inside one hyperedge of H. -/
def RelationsCoveredBy
    {L : RelLanguage.{u}} (H : Set (Set W))
    (R : RelStructure L W) : Prop :=
  ∀ (sym : L.Symbol) (x : Fin (L.arity sym) → W),
    R.rel sym x →
      ∃ e : Set W, e ∈ H ∧ ∀ i, x i ∈ e

/-- High-girth support controls every irreducible induced substructure:
if relation tuples are edge-supported and every ambient vertex lies in a
support edge, then every irreducible induced substructure lies in one edge. -/
theorem irreducible_induce_subset_edge_of_girthGT_three
    {L : RelLanguage.{u}} {R : RelStructure L W}
    {H : Set (Set W)}
    (hgt : GirthGT H 3)
    (hRel : RelationsCoveredBy H R)
    (hH : H.Nonempty)
    (hVert : ∀ x : W, ∃ e : Set W, e ∈ H ∧ x ∈ e)
    {S : Set W}
    (hIrr : (R.induce S).Irreducible) :
    ∃ e : Set W, e ∈ H ∧ ∀ z : S, z.1 ∈ e := by
  by_cases hsub : S.Subsingleton
  · by_cases hne : S.Nonempty
    · rcases hne with ⟨x, hx⟩
      obtain ⟨e, he, hxe⟩ := hVert x
      refine ⟨e, he, ?_⟩
      intro z
      have hzx : z.1 = x := hsub z.2 hx
      simpa [hzx] using hxe
    · obtain ⟨e, he⟩ := hH
      refine ⟨e, he, ?_⟩
      intro z
      exact (hne ⟨z.1, z.2⟩).elim
  · have hnon : S.Nontrivial := by
      rw [← Set.not_subsingleton_iff]
      exact hsub
    have hPair : PairCoveredBy H S := by
      intro x y hx hy hxy
      let xs : S := ⟨x, hx⟩
      let ys : S := ⟨y, hy⟩
      have hxyS : xs ≠ ys := by
        intro h
        apply hxy
        exact congrArg Subtype.val h
      obtain ⟨sym, t, i, j, ht, hi, hj⟩ := hIrr hxyS
      have htR : R.rel sym (Subtype.val ∘ t) := ht
      obtain ⟨e, he, hte⟩ := hRel sym (Subtype.val ∘ t) htR
      refine ⟨e, he, ?_, ?_⟩
      · have := hte i
        change t i |>.1 ∈ e at this
        simpa [xs, hi] using this
      · have := hte j
        change t j |>.1 ∈ e at this
        simpa [ys, hj] using this
    obtain ⟨e, he, hSe⟩ :=
      pairCovered_subset_edge_of_girthGT_three hgt hnon hPair
    exact ⟨e, he, fun z => hSe z.2⟩
end StructuralRamsey.Girth

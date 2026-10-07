import Girth.ForestFreshCarrier
import Girth.Berge
import Mathlib.Tactic

/-!
# Pair-shadow cliques in hypergraphs of girth greater than three

When a linear support has no Berge triangle, every clique of its two-shadow
lies inside a single support edge. This makes the boundary of a new B-piece
against an A-pair-closed base a permitted single separator, PROVIDED the
new piece has no nonedge vertex pair in the old base (such a pair would
already determine a B-copy owner).

The geometric result is unconditional under its stated hypotheses.
It does not construct a globally evaluated free successor-tree history.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- Three different edges meeting cyclically in three different vertices
form a Berge triangle. -/
theorem no_three_distinct_edges_in_triangle
    {E : Set (Set W)} (hgt : GirthGT E 3)
    {e f g : Set W}
    (he : e ∈ E) (hf : f ∈ E) (hg : g ∈ E)
    (hef : e ≠ f) (hfg : f ≠ g) (hge : g ≠ e)
    {x y z : W}
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hxe : x ∈ e) (hye : y ∈ e)
    (hyf : y ∈ f) (hzf : z ∈ f)
    (hzg : z ∈ g) (hxg : x ∈ g) :
    False := by
  let c : BergeCycle E := {
    length := 3
    hlength := by omega
    edge := ![e, f, g]
    vertex := ![y, z, x]
    edge_mem := by
      intro i
      fin_cases i
      · exact he
      · exact hf
      · exact hg
    edge_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    vertex_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    left_mem := by
      intro i
      fin_cases i
      · exact hye
      · exact hzf
      · exact hxg
    right_mem := by
      intro i
      fin_cases i
      · simpa [cyclicSucc] using hyf
      · simpa [cyclicSucc] using hzg
      · simpa [cyclicSucc] using hxe
  }
  exact hgt ⟨c, by simp [c]⟩

/-- Fix one edge e covering an initial pair of a clique in the 2-shadow.
The triangle-free condition forces every other member of the clique
to lie in that same edge. -/
theorem shadowClique_subset_edge
    {E : Set (Set W)} (hgt : GirthGT E 3)
    {S : Set W}
    (hPairs : ∀ ⦃x y : W⦄, x ∈ S → y ∈ S → x ≠ y →
      ∃ e : Set W, e ∈ E ∧ x ∈ e ∧ y ∈ e)
    {e : Set W} (he : e ∈ E)
    {x y : W}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hxe : x ∈ e) (hye : y ∈ e) :
    S ⊆ e := by
  intro z hz
  by_contra hzne
  have hyz : y ≠ z := by
    intro h
    subst z
    exact hzne hye
  have hzx : z ≠ x := by
    intro h
    subst z
    exact hzne hxe
  obtain ⟨f, hf, hyf, hzf⟩ := hPairs hy hz hyz
  obtain ⟨g, hg, hzg, hxg⟩ := hPairs hz hx hzx
  have hef : e ≠ f := by
    intro heq
    apply hzne
    simpa [heq] using hzf
  have hge : g ≠ e := by
    intro hgeq
    apply hzne
    simpa [hgeq] using hzg
  have hfg : f ≠ g := by
    intro hfgEq
    have hxF : x ∈ f := by
      rw [hfgEq]
      exact hxg
    have hlin : GirthGT E 2 :=
      girthGT_mono hgt (by omega)
    have hsmall : (e ∩ f).Subsingleton :=
      pairwise_subsingleton_of_girthGT_two hlin he hf hef
    exact hxy (hsmall ⟨hxe, hxF⟩ ⟨hye, hyf⟩)
  exact no_three_distinct_edges_in_triangle
    hgt he hf hg hef hfg hge hxy hyz hzx
    hxe hye hyf hzf hzg hxg

/-- The pair-shadow clique property has an edge witness as soon as
the set has two distinct vertices. -/
theorem shadowClique_contained_in_edge
    {E : Set (Set W)} (hgt : GirthGT E 3)
    {S : Set W}
    (hPairs : ∀ ⦃x y : W⦄, x ∈ S → y ∈ S → x ≠ y →
      ∃ e : Set W, e ∈ E ∧ x ∈ e ∧ y ∈ e)
    {x y : W}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ∃ e : Set W, e ∈ E ∧ S ⊆ e := by
  obtain ⟨e, he, hxe, hye⟩ := hPairs hx hy hxy
  exact ⟨e, he, shadowClique_subset_edge hgt hPairs he hx hy hxy hxe hye⟩

/-- Pair closure for support edges plus exclusion of old nonedge B-owners
forces the boundary of a genuinely new B-piece to be one complete
A-edge, rather than an arbitrary multivertex overlap. -/
theorem piece_boundary_is_whole_edge_of_two
    (F : HypergraphPiece W) (D : Set W)
    (hGirth : GirthGT F.edges 3)
    (hNoNonedgePair :
      ∀ ⦃x y : W⦄,
        x ∈ F.carrier ∩ D → y ∈ F.carrier ∩ D → x ≠ y →
        ∃ e : Set W, e ∈ F.edges ∧ x ∈ e ∧ y ∈ e)
    (hEdgeClosed :
      ∀ ⦃e : Set W⦄, e ∈ F.edges →
        ¬ (e ∩ D).Subsingleton → e ⊆ D)
    {x y : W}
    (hx : x ∈ F.carrier ∩ D)
    (hy : y ∈ F.carrier ∩ D)
    (hxy : x ≠ y) :
    ∃ e : Set W, e ∈ F.edges ∧ F.carrier ∩ D = e := by
  obtain ⟨e, he, hBound⟩ :=
    shadowClique_contained_in_edge hGirth hNoNonedgePair hx hy hxy
  have hxe : x ∈ e := hBound hx
  have hye : y ∈ e := hBound hy
  have hbig : ¬ (e ∩ D).Subsingleton := by
    intro hsmall
    exact hxy (hsmall ⟨hxe, hx.2⟩ ⟨hye, hy.2⟩)
  have heD : e ⊆ D := hEdgeClosed he hbig
  apply Exists.intro e
  refine ⟨he, ?_⟩
  apply Set.Subset.antisymm hBound
  intro z hz
  exact ⟨F.edge_subset he hz, heD hz⟩

end StructuralRamsey.Girth

import Girth.SharedBoundaryIncidence
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # A leaf hyperedge in a linear Berge forest

For a finite linear labelled hypergraph whose incidence graph is acyclic,
some hyperedge meets the union of all remaining hyperedges in at most one
vertex.  This is the leaf-elimination statement needed to build a join tree
on the hyperedges.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- A finite linear family with acyclic incidence graph has a leaf hyperedge:
one whose intersection with the union of all other hyperedges is
subsingleton. -/
theorem exists_leaf_edge_of_incidence_acyclic
    [Fintype E] [Nonempty E]
    (edge : E → Set W)
    (hLinear : LabelledEdgeLinear edge)
    (hAcyclic : (boundaryIncidenceGraph edge).IsAcyclic) :
    ∃ e : E,
      (edge e ∩
        ⋃ f : {f : E // f ≠ e}, edge f.1).Subsingleton := by
  classical
  have hFiniteShared :
      Finite (SharedBoundaryVertex edge) :=
    finite_sharedBoundaryVertex edge hLinear
  letI : Finite (SharedBoundaryVertex edge) := hFiniteShared
  letI : Fintype (SharedBoundaryVertex edge) :=
    Fintype.ofFinite (SharedBoundaryVertex edge)
  let SG :=
    boundaryIncidenceGraph (sharedBoundaryEdge edge)
  have hSGAcyclic : SG.IsAcyclic := by
    exact sharedBoundaryIncidence_isAcyclic edge hAcyclic
  let e0 : E := Classical.choice (inferInstance : Nonempty E)
  by_cases hShared0 :
      ∃ x : SharedBoundaryVertex edge, x.1 ∈ edge e0
  · rcases hShared0 with ⟨x0, hx0⟩
    let C : SG.ConnectedComponent :=
      SG.connectedComponentMk (Sum.inl e0)
    have he0C : (Sum.inl e0 : E ⊕ SharedBoundaryVertex edge) ∈ C := by
      exact C.connectedComponentMk_mem
    have hAdj0 :
        SG.Adj (Sum.inl e0) (Sum.inr x0) := by
      exact hx0
    have hx0C :
        (Sum.inr x0 : E ⊕ SharedBoundaryVertex edge) ∈ C :=
      C.mem_supp_of_adj_mem_supp he0C hAdj0
    let e0C : C := ⟨Sum.inl e0, he0C⟩
    let x0C : C := ⟨Sum.inr x0, hx0C⟩
    have hneC : e0C ≠ x0C := by
      intro h
      have hv := congrArg Subtype.val h
      simp [e0C, x0C] at hv
    letI : Nontrivial C :=
      ⟨⟨e0C, x0C, hneC⟩⟩
    letI : DecidableRel C.toSimpleGraph.Adj :=
      Classical.decRel _
    have hTree : C.toSimpleGraph.IsTree :=
      hSGAcyclic.isTree_connectedComponent C
    obtain ⟨v, hvdeg⟩ :=
      hTree.exists_vert_degree_one_of_nontrivial
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hvdeg
    rcases hvdeg with ⟨u, hvu, huniq⟩
    rcases v with ⟨v, hvC⟩
    cases v with
    | inl e =>
        refine ⟨e, ?_⟩
        intro x hx y hy
        rcases Set.mem_iUnion.mp hx.2 with ⟨fx, hfx⟩
        rcases Set.mem_iUnion.mp hy.2 with ⟨fy, hfy⟩
        let sx : SharedBoundaryVertex edge :=
          ⟨x, ⟨e, fx.1, fx.2.symm, hx.1, hfx⟩⟩
        let sy : SharedBoundaryVertex edge :=
          ⟨y, ⟨e, fy.1, fy.2.symm, hy.1, hfy⟩⟩
        have hsxAdj :
            SG.Adj (Sum.inl e) (Sum.inr sx) := by
          exact hx.1
        have hsyAdj :
            SG.Adj (Sum.inl e) (Sum.inr sy) := by
          exact hy.1
        have hsxC :
            (Sum.inr sx : E ⊕ SharedBoundaryVertex edge) ∈ C :=
          C.mem_supp_of_adj_mem_supp hvC hsxAdj
        have hsyC :
            (Sum.inr sy : E ⊕ SharedBoundaryVertex edge) ∈ C :=
          C.mem_supp_of_adj_mem_supp hvC hsyAdj
        let sxC : C := ⟨Sum.inr sx, hsxC⟩
        let syC : C := ⟨Sum.inr sy, hsyC⟩
        have hsxAdjC :
            C.toSimpleGraph.Adj
              ⟨Sum.inl e, hvC⟩ sxC :=
          hsxAdj
        have hsyAdjC :
            C.toSimpleGraph.Adj
              ⟨Sum.inl e, hvC⟩ syC :=
          hsyAdj
        have hsxyC : sxC = syC :=
          (huniq sxC hsxAdjC).trans
            (huniq syC hsyAdjC).symm
        have hsxySum :
            (Sum.inr sx : E ⊕ SharedBoundaryVertex edge) =
              Sum.inr sy :=
          congrArg Subtype.val hsxyC
        have hsxy : sx = sy :=
          Sum.inr.inj hsxySum
        exact congrArg Subtype.val hsxy
    | inr x =>
        exfalso
        rcases x.2 with ⟨e, f, hef, hxe, hxf⟩
        have heAdj :
            SG.Adj (Sum.inr x) (Sum.inl e) := by
          exact hxe
        have hfAdj :
            SG.Adj (Sum.inr x) (Sum.inl f) := by
          exact hxf
        have heC :
            (Sum.inl e : E ⊕ SharedBoundaryVertex edge) ∈ C :=
          C.mem_supp_of_adj_mem_supp hvC heAdj
        have hfC :
            (Sum.inl f : E ⊕ SharedBoundaryVertex edge) ∈ C :=
          C.mem_supp_of_adj_mem_supp hvC hfAdj
        let eC : C := ⟨Sum.inl e, heC⟩
        let fC : C := ⟨Sum.inl f, hfC⟩
        have heAdjC :
            C.toSimpleGraph.Adj
              ⟨Sum.inr x, hvC⟩ eC :=
          heAdj
        have hfAdjC :
            C.toSimpleGraph.Adj
              ⟨Sum.inr x, hvC⟩ fC :=
          hfAdj
        have hefC : eC = fC :=
          (huniq eC heAdjC).trans
            (huniq fC hfAdjC).symm
        have hefSum :
            (Sum.inl e : E ⊕ SharedBoundaryVertex edge) =
              Sum.inl f :=
          congrArg Subtype.val hefC
        exact hef (Sum.inl.inj hefSum)
  · refine ⟨e0, ?_⟩
    intro x hx y hy
    exfalso
    rcases Set.mem_iUnion.mp hx.2 with ⟨f, hxf⟩
    let sx : SharedBoundaryVertex edge :=
      ⟨x, ⟨e0, f.1, f.2.symm, hx.1, hxf⟩⟩
    exact hShared0 ⟨sx, hx.1⟩

end StructuralRamsey.Girth

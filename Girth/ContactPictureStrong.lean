import Girth.ContactTaggedPicture

/-! Strong inducedness and edge linearity of the free amalgam.
At a linear base, the active strip is strongly induced in the old
picture. This gives the exact hypothesis on partial gluing maps below.
No global wagon or system-girth bound on the output is used. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P U F J R V₀ E₀ I₀ P₀ : Type v}

namespace ContactCarrierEmbedding
variable {D : OrderOneData V E I P} {H : OrderOneData U F J R}
    (M : ContactCarrierEmbedding D H)

theorem common_two_edges_eq
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    {e f : E} {x y : U}
    (hxy : x ≠ y)
    (hxe : x ∈ H.edgeCarrier (M.edge e)) (hye : y ∈ H.edgeCarrier (M.edge e))
    (hxf : x ∈ H.edgeCarrier (M.edge f)) (hyf : y ∈ H.edgeCarrier (M.edge f)) :
    e = f := by
  classical
  by_contra hne
  obtain ⟨a,rfl⟩ := M.edge_vertex_range hxe
  obtain ⟨b,rfl⟩ := M.edge_vertex_range hye
  exact hxy (congrArg M.vertex (hlin e f hne
    ⟨M.edge_vertex_reflect e a hxe,M.edge_vertex_reflect f a hxf⟩
    ⟨M.edge_vertex_reflect e b hye,M.edge_vertex_reflect f b hyf⟩))

end ContactCarrierEmbedding

namespace ContactPictureData
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F J R} (A : ContactPictureData D L H)

/-- Strong inducedness of the core in the output, the conclusion of
picture lemma (a) concerning the active strip. -/
def CoreStrong : Prop :=
  ∀ f : F, (H.edgeCarrier f ∩ Set.range A.core.vertex).Nontrivial →
    f ∈ Set.range A.core.edge

def StandardStrong : Prop :=
  ∀ i f, (H.edgeCarrier f ∩ A.standard i).Nontrivial →
    f ∈ Set.range (A.std i).edge

/-- Core strongness and G1 imply all standards are strongly induced.
The common-core condition rules out an edge outside both sources
meeting a standard twice. -/
theorem standard_strong (hc : A.CoreStrong) (h1 : D.ContactG1) :
    A.StandardStrong := by
  classical
  intro i f hn
  obtain ⟨x,hx,y,hy,hxy⟩ := hn
  have coreCase : f ∈ Set.range A.core.edge →
      f ∈ Set.range (A.std i).edge := by
    rintro ⟨e,rfl⟩
    obtain ⟨a,rfl⟩ := A.core.edge_vertex_range hx.1
    obtain ⟨b,rfl⟩ := A.core.edge_vertex_range hy.1
    have hab : a ≠ b := fun he => hxy (congrArg A.core.vertex he)
    exact (A.std_core_edge i e).mpr (h1.strong i e
      ⟨a,⟨A.core.edge_vertex_reflect e a hx.1,(A.std_core_vertex i a).mp hx.2⟩,
       b,⟨A.core.edge_vertex_reflect e b hy.1,(A.std_core_vertex i b).mp hy.2⟩,hab⟩)
  rcases A.edge_cover f with h | ⟨j,e,rfl⟩
  · exact coreCase h
  · by_cases hij : i = j
    · subst j
      exact ⟨e,rfl⟩
    · apply coreCase
      exact hc _ ⟨x,⟨hx.1,A.shared_vertex i j hij x hx.2
        ((A.std j).edge_vertex_range hx.1)⟩,
        y,⟨hy.1,A.shared_vertex i j hij y hy.2
        ((A.std j).edge_vertex_range hy.1)⟩,hxy⟩

/-- Edges of the output are linear once the core and all standards
are strongly induced and linear. -/
theorem edge_linearity (hc : A.CoreStrong) (hs : A.StandardStrong)
    (hD : D.ContactLinear) (hL : L.ContactLinear) :
    ∀ e f : F, e ≠ f → (H.edgeCarrier e ∩ H.edgeCarrier f).Subsingleton := by
  classical
  intro e f hef x hx y hy
  by_contra hxy
  rcases A.edge_cover e with ⟨a,rfl⟩ | ⟨i,a,rfl⟩
  · have hf : f ∈ Set.range A.core.edge :=
      hc f ⟨x,⟨hx.2,A.core.edge_vertex_range hx.1⟩,
        y,⟨hy.2,A.core.edge_vertex_range hy.1⟩,hxy⟩
    obtain ⟨b,rfl⟩ := hf
    exact hef (congrArg A.core.edge
      (A.core.common_two_edges_eq hD.1 hxy hx.1 hy.1 hx.2 hy.2))
  · have hf : f ∈ Set.range (A.std i).edge :=
      hs i f ⟨x,⟨hx.2,(A.std i).edge_vertex_range hx.1⟩,
        y,⟨hy.2,(A.std i).edge_vertex_range hy.1⟩,hxy⟩
    obtain ⟨b,rfl⟩ := hf
    exact hef (congrArg (A.std i).edge
      ((A.std i).common_two_edges_eq hL.1 hxy hx.1 hy.1 hx.2 hy.2))

end ContactPictureData

namespace ContactTaggedPicture
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    (T : ContactTaggedPicture D L)

def StripStrong : Prop :=
  ∀ i f, (L.edgeCarrier f ∩ {x | ∃ a, T.vertexGlue i x = some a}).Nontrivial →
    ∃ e, T.edgeGlue i f = some e

/-- The old strip is strongly induced in the old picture. Hence an
output edge having two core vertices is actually a core edge. -/
theorem core_strong (h : T.StripStrong) : T.toPictureData.CoreStrong := by
  classical
  intro e hn
  obtain ⟨x,hx,y,hy,hxy⟩ := hn
  rcases T.toPictureData.edge_cover e with hcore | ⟨i,f,rfl⟩
  · exact hcore
  · have hxm : x ∈ T.stdV i '' L.edgeCarrier f := by
      rw [← T.output_carrier_standard i f]
      exact hx.1
    have hym : y ∈ T.stdV i '' L.edgeCarrier f := by
      rw [← T.output_carrier_standard i f]
      exact hy.1
    obtain ⟨a,ha,rfl⟩ := hxm
    obtain ⟨b,hb,rfl⟩ := hym
    obtain ⟨u,hu⟩ := hx.2
    obtain ⟨v,hv⟩ := hy.2
    have hga : T.vertexGlue i a = some u :=
      (contactStandardEmb_eq_core T.vertexGlue T.vertex_inj i a u).mp hu.symm
    have hgb : T.vertexGlue i b = some v :=
      (contactStandardEmb_eq_core T.vertexGlue T.vertex_inj i b v).mp hv.symm
    obtain ⟨d,hd⟩ := h i f
      ⟨a,⟨ha,⟨u,hga⟩⟩,b,⟨hb,⟨v,hgb⟩⟩,fun he => hxy (congrArg (T.stdV i) he)⟩
    exact ⟨d,((contactStandardEmb_eq_core T.edgeGlue T.edge_inj i f d).mpr hd).symm⟩

end ContactTaggedPicture
end StructuralRamsey.Girth

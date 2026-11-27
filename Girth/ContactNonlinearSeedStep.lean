import Girth.ContactActualPictureStep
import Girth.ContactProjectionPreservation

/-! The nonlinear-base picture step of the elementary linear-seed
construction. No strongness of the core in the output is asserted:
it need not hold over a nonlinear base. Instead, common vertices
of different core copies in two parts lie on a common actual edge.
This suffices for strongness of every standard and output linearity.

For this seed construction the old picture can have an empty
designated-copy type; the target embeddings are carried separately.
The projection's designated-copy axioms are then vacuous, so the
same literal strip and gluing construction applies. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I V₀ E₀ I₀ X B : Type v}

namespace ContactTrainStrip
variable {m : ℕ} {D : ContactHypergraphData V E I}
    {L : ContactHypergraphData V₀ E₀ I₀}
    {T : ContactTrainData E m} {S : ContactTrainData E₀ m}
    (A : ContactTrainStrip D L T S)

/-- The core-copy intersection hypothesis in picture lemma (b).
It is a statement about two different projected parts, not two
arbitrary vertices of the intersection. -/
def TwoPartIntersection (_A : ContactTrainStrip D L T S) (p : V → X) : Prop :=
  ∀ i j : I, i ≠ j → ∀ u v : V,
    u ∈ D.copyCarrier i → u ∈ D.copyCarrier j →
    v ∈ D.copyCarrier i → v ∈ D.copyCarrier j → p u ≠ p v →
      ∃ e, e ∈ D.copyEdges i ∧ e ∈ D.copyEdges j ∧
        D.copyCarrier i ∩ D.copyCarrier j = D.edgeCarrier e

/-- The two-part intersection alternative suffices for every
standard to be strongly induced, even when the core is not. -/
theorem nonlinear_standard_strong
    {base : B → Set X} (P : ContactBaseProjection L base) (b : B) (p : V → X)
    (hc : A.CoreOver P b p)
    (hpair : A.TwoPartIntersection p)
    (hstrong : ∀ i e, (D.edgeCarrier e ∩ D.copyCarrier i).Nontrivial →
      e ∈ D.copyEdges i)
    (hL : ∀ e f : E₀, e ≠ f → (L.edgeCarrier e ∩ L.edgeCarrier f).Subsingleton) :
    A.bottomPicture.toPictureData.StandardStrong := by
  classical
  let Q := A.bottomPicture.toPictureData
  intro i f hn
  obtain ⟨x,hx,y,hy,hxy⟩ := hn
  have coreCase : f ∈ Set.range Q.core.edge → f ∈ Set.range (Q.std i).edge := by
    rintro ⟨e,rfl⟩
    obtain ⟨u,rfl⟩ := Q.core.edge_vertex_range hx.1
    obtain ⟨v,rfl⟩ := Q.core.edge_vertex_range hy.1
    have huv : u ≠ v := fun he => hxy (congrArg Q.core.vertex he)
    exact (Q.std_core_edge i e).mpr (hstrong i e
      ⟨u,⟨Q.core.edge_vertex_reflect e u hx.1,(Q.std_core_vertex i u).mp hx.2⟩,
       v,⟨Q.core.edge_vertex_reflect e v hy.1,(Q.std_core_vertex i v).mp hy.2⟩,huv⟩)
  rcases Q.edge_cover f with h | ⟨j,g,rfl⟩
  · exact coreCase h
  · by_cases hij : i = j
    · subst j
      exact ⟨g,rfl⟩
    · obtain ⟨u,hu⟩ := Q.shared_vertex i j hij x hx.2
        ((Q.std j).edge_vertex_range hx.1)
      obtain ⟨v,hv⟩ := Q.shared_vertex i j hij y hy.2
        ((Q.std j).edge_vertex_range hy.1)
      have hui := (Q.std_core_vertex i u).mp (hu.symm ▸ hx.2)
      have huj := (Q.std_core_vertex j u).mp (hu.symm ▸ (Q.std j).edge_vertex_range hx.1)
      have hvi := (Q.std_core_vertex i v).mp (hv.symm ▸ hy.2)
      have hvj := (Q.std_core_vertex j v).mp (hv.symm ▸ (Q.std j).edge_vertex_range hy.1)
      obtain ⟨a,ha⟩ := (Q.std j).edge_vertex_range hx.1
      obtain ⟨c,hc'⟩ := (Q.std j).edge_vertex_range hy.1
      have hag := (Q.std j).edge_vertex_reflect g a (ha.symm ▸ hx.1)
      have hcg := (Q.std j).edge_vertex_reflect g c (hc'.symm ▸ hy.1)
      have hne : a ≠ c := fun he => hxy (ha.symm.trans ((congrArg (Q.std j).vertex he).trans hc'))
      have hap : p u = P.vertex a := by
        have he : A.stdV j a = A.coreV u := ha.trans hu.symm
        exact hc.vertex_compatible j a u ((contactStandardEmb_eq_core A.vertexGlue A.vertex_inj j a u).mp he)
      have hcp : p v = P.vertex c := by
        have he : A.stdV j c = A.coreV v := hc'.trans hv.symm
        exact hc.vertex_compatible j c v ((contactStandardEmb_eq_core A.vertexGlue A.vertex_inj j c v).mp he)
      have hpne : p u ≠ p v := fun he => hne (P.edge_inj g hag hcg (hap.symm.trans (he.trans hcp)))
      obtain ⟨e,hei,hej,hcar⟩ := hpair i j hij u v hui huj hvi hvj hpne
      obtain ⟨g',hg'⟩ := (Q.std_core_edge j e).mpr hej
      have hue : u ∈ D.edgeCarrier e := hcar ▸ (show u ∈ D.copyCarrier i ∩ D.copyCarrier j from ⟨hui,huj⟩)
      have hve : v ∈ D.edgeCarrier e := hcar ▸ (show v ∈ D.copyCarrier i ∩ D.copyCarrier j from ⟨hvi,hvj⟩)
      have hxe : x ∈ A.bottomPicture.output.edgeCarrier (Q.core.edge e) := by
        rw [Q.core.edge_carrier]
        exact ⟨u,hue,hu⟩
      have hye : y ∈ A.bottomPicture.output.edgeCarrier (Q.core.edge e) := by
        rw [Q.core.edge_carrier]
        exact ⟨v,hve,hv⟩
      have hgEq : g = g' := (Q.std j).common_two_edges_eq hL hxy hx.1 hy.1
        (hg'.symm ▸ hxe) (hg'.symm ▸ hye)
      have hEq : (Q.std j).edge g = Q.core.edge e := (congrArg (Q.std j).edge hgEq).trans hg'
      exact hEq.symm ▸ (Q.std_core_edge i e).mpr hei

/-- Linearity of the nonlinear-base output. An edge of the core
meeting a standard edge in two points belongs to that standard,
by strongness of the core copy. The two edges then coincide by
old linearity. Two core edges are compared inside the core. -/
theorem nonlinear_output_linear
    (hs : A.bottomPicture.toPictureData.StandardStrong)
    (hstrong : ∀ i e, (D.edgeCarrier e ∩ D.copyCarrier i).Nontrivial →
      e ∈ D.copyEdges i)
    (hD : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (hL : ∀ e f : E₀, e ≠ f → (L.edgeCarrier e ∩ L.edgeCarrier f).Subsingleton) :
    ∀ e f : A.Edge, e ≠ f →
      (A.outputHypergraph.edgeCarrier e ∩ A.outputHypergraph.edgeCarrier f).Subsingleton := by
  classical
  let Q := A.bottomPicture.toPictureData
  intro e f hne x hx y hy
  by_contra hxy
  have hxe : x ∈ A.bottomPicture.output.edgeCarrier e := by rw [A.bottomPicture_output_eq]; exact hx.1
  have hxf : x ∈ A.bottomPicture.output.edgeCarrier f := by rw [A.bottomPicture_output_eq]; exact hx.2
  have hye : y ∈ A.bottomPicture.output.edgeCarrier e := by rw [A.bottomPicture_output_eq]; exact hy.1
  have hyf : y ∈ A.bottomPicture.output.edgeCarrier f := by rw [A.bottomPicture_output_eq]; exact hy.2
  have sameStd (i : I) (a : E₀) (b : A.Edge)
      (hx₁ : x ∈ A.bottomPicture.output.edgeCarrier ((Q.std i).edge a))
      (hy₁ : y ∈ A.bottomPicture.output.edgeCarrier ((Q.std i).edge a))
      (hx₂ : x ∈ A.bottomPicture.output.edgeCarrier b)
      (hy₂ : y ∈ A.bottomPicture.output.edgeCarrier b) :
      (Q.std i).edge a = b := by
    obtain ⟨c,rfl⟩ := hs i b
      ⟨x,⟨hx₂,(Q.std i).edge_vertex_range hx₁⟩,
       y,⟨hy₂,(Q.std i).edge_vertex_range hy₁⟩,hxy⟩
    exact congrArg (Q.std i).edge ((Q.std i).common_two_edges_eq hL hxy hx₁ hy₁ hx₂ hy₂)
  rcases Q.edge_cover e with ⟨a,rfl⟩ | ⟨i,a,rfl⟩
  · rcases Q.edge_cover f with ⟨b,rfl⟩ | ⟨i,b,rfl⟩
    · exact hne (congrArg Q.core.edge (Q.core.common_two_edges_eq hD hxy hxe hye hxf hyf))
    · exact hne (sameStd i b _ hxf hyf hxe hye).symm
  · exact hne (sameStd i a _ hxe hye hxf hyf)

end ContactTrainStrip
end StructuralRamsey.Girth

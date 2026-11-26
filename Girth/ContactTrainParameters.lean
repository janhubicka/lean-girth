import Girth.ContactGeneratedTrain
import Girth.ContactPictureData

/-! Train parameters on two levels. For two edges in one coarser
wagon meeting at a vertex outside the allowed parts, their finer
parents must agree. This edge formulation is exactly the usual
sibling-wagon intersection condition, by taking incident edges. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I V₀ E₀ I₀ : Type v}

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)

def Parameter {m : ℕ} (T : ContactTrainData E m)
    (μ ν : Fin (m+1)) (allowed : Set V) : Prop :=
  ∀ e f x, T.parent ν e = T.parent ν f →
    x ∈ D.edgeCarrier e → x ∈ D.edgeCarrier f → x ∉ allowed →
    T.parent μ e = T.parent μ f

theorem parameter_iff_wagon_intersection {m : ℕ} (T : ContactTrainData E m)
    (μ ν : Fin (m+1)) (hle : μ ≤ ν) (allowed : Set V) :
    D.Parameter T μ ν allowed ↔
      ∀ e f : E, T.parent ν e = T.parent ν f → T.parent μ e ≠ T.parent μ f →
        ((D.atCut (T.parent μ)).contactWagonCarrier (T.parent μ e) ∩
          (D.atCut (T.parent μ)).contactWagonCarrier (T.parent μ f)) ⊆ allowed := by
  classical
  constructor
  · intro h e f hef hne x hx
    by_contra hn
    obtain ⟨g,hg,hgx⟩ := hx.1
    obtain ⟨k,hk,hkx⟩ := hx.2
    have hν : T.parent ν g = T.parent ν k :=
      (T.nested μ ν hle _ _ hg).trans
        (hef.trans (T.nested μ ν hle _ _ hk).symm)
    exact hne (hg.symm.trans ((h g k x hν hgx hkx hn).trans hk))
  · intro h e f x hef hxe hxf hx
    by_contra hn
    exact hx (h e f hef hn ⟨⟨e,rfl,hxe⟩,⟨f,rfl,hxf⟩⟩)

end ContactHypergraphData

namespace ContactTrainStrip
variable {m : ℕ}
    {D : ContactHypergraphData V E I} {L : ContactHypergraphData V₀ E₀ I₀}
    {T : ContactTrainData E m} {S : ContactTrainData E₀ m}
    (A : ContactTrainStrip D L T S)

/-- The bridge into a core copy, expressed uniformly at the top
and positive proper levels. At a proper level G1 supplies the
incident shared edge. At the top only the fact that the copy has
no isolated vertices is needed. -/
def CoreBridgeAt (ν : Fin (m+1)) : Prop :=
  ∀ i p x, x ∈ D.copyCarrier i →
    x ∈ (D.atCut (T.parent ν)).contactWagonCarrier p →
    (D.atCut (T.parent ν)).contactMeets i p →
    ∃ e, e ∈ D.copyEdges i ∧ T.parent ν e = p ∧ x ∈ D.edgeCarrier e

theorem coreBridgeAt_of_g1 (ν : Fin (m+1))
    (h1 : (D.atCut (T.parent ν)).ContactG1) :
    A.CoreBridgeAt ν :=
  fun i p x hx hxp hm => h1.bridge i p (Or.inl hm) x hx hxp

theorem coreBridgeAt_top (hcover : ∀ i x, x ∈ D.copyCarrier i →
      ∃ e, e ∈ D.copyEdges i ∧ x ∈ D.edgeCarrier e) :
    A.CoreBridgeAt ⟨m,by omega⟩ := by
  intro i p x hx hxp hm
  obtain ⟨e,he,hxe⟩ := hcover i x hx
  obtain ⟨f,hf,hfp⟩ := hm
  exact ⟨e,he,(T.top e f).trans hfp,hxe⟩

/-- A common vertex in two different standards of the same output
wagon is an actual core vertex in the corresponding core wagon.
This is the only use of G2 in parameter preservation. -/
theorem common_core_vertex_wagon (ν : Fin (m+1))
    (h2 : (D.atCut (T.parent ν)).ContactG2)
    (i j : I) (hij : i ≠ j) (f g : E₀) (u : A.Vertex)
    (huf : u ∈ A.outputHypergraph.edgeCarrier (A.stdE i f))
    (hug : u ∈ A.outputHypergraph.edgeCarrier (A.stdE j g))
    (hp : A.parentAt ν (A.stdE i f) = A.parentAt ν (A.stdE j g)) :
    ∃ x : V, ∃ p : T.Wagon ν,
      A.coreV x = u ∧ A.coreW ν p = A.parentAt ν (A.stdE i f) ∧
      x ∈ (D.atCut (T.parent ν)).contactWagonCarrier p := by
  let P := (A.atCut ν).toPictureData
  have huf' : u ∈ (A.atCut ν).output.edgeCarrier ((A.atCut ν).stdE i f) := huf
  have hug' : u ∈ (A.atCut ν).output.edgeCarrier ((A.atCut ν).stdE j g) := hug
  obtain ⟨x,hx⟩ := P.shared_vertex i j hij u
    ((P.std i).edge_vertex_range huf') ((P.std j).edge_vertex_range hug')
  let w := A.parentAt ν (A.stdE i f)
  have hiW : w ∈ Set.range (P.std i).wagon := by
    refine ⟨S.parent ν f,?_⟩
    exact (A.parentAt_std ν i f).symm
  have hjW : w ∈ Set.range (P.std j).wagon := by
    refine ⟨S.parent ν g,?_⟩
    exact (A.parentAt_std ν j g).symm.trans hp.symm
  obtain ⟨p,hp'⟩ := P.shared_wagon i j hij w hiW hjW
  have hxi : x ∈ D.copyCarrier i := (P.std_core_vertex i x).mp
    (hx.symm ▸ (P.std i).edge_vertex_range huf')
  have hxj : x ∈ D.copyCarrier j := (P.std_core_vertex j x).mp
    (hx.symm ▸ (P.std j).edge_vertex_range hug')
  have hpi := (P.std_core_wagon i p).mp (hp'.symm ▸ hiW)
  have hpj := (P.std_core_wagon j p).mp (hp'.symm ▸ hjW)
  obtain ⟨r,hr,hr'⟩ := (D.atCut (T.parent ν)).contact_shared_pair_in_wagon h2
    (a := Sum.inl i) (b := Sum.inl j)
    (by intro he; exact hij (Sum.inl.inj he))
    (x := Sum.inl x) (y := Sum.inr p) (by intro he; cases he)
    hxi hpi hxj hpj
  have he : p = r := hr'
  subst r
  exact ⟨x,p,hx,hp',hr⟩

end ContactTrainStrip
end StructuralRamsey.Girth

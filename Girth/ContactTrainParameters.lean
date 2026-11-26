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
def CoreBridgeAt (_A : ContactTrainStrip D L T S) (ν : Fin (m+1)) : Prop :=
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
  have huf' : u ∈ (A.atCut ν).output.edgeCarrier ((A.atCut ν).stdE i f) := by
    rw [A.cut_output_eq ν]
    exact huf
  have hug' : u ∈ (A.atCut ν).output.edgeCarrier ((A.atCut ν).stdE j g) := by
    rw [A.cut_output_eq ν]
    exact hug
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


/-- The top-level variant of the common mixed pair lemma. Because
there is only one top wagon, a shared vertex in a core copy lies
on a core edge in that wagon by the ordinary no-isolated-vertices
condition. No G2 assumption is made at the top. -/
theorem common_core_vertex_wagon_top
    (hcover : ∀ i x, x ∈ D.copyCarrier i →
      ∃ e, e ∈ D.copyEdges i ∧ x ∈ D.edgeCarrier e)
    (i j : I) (hij : i ≠ j) (f g : E₀) (u : A.Vertex)
    (huf : u ∈ A.outputHypergraph.edgeCarrier (A.stdE i f))
    (hug : u ∈ A.outputHypergraph.edgeCarrier (A.stdE j g)) :
    ∃ x : V, ∃ p : T.Wagon ⟨m,by omega⟩,
      A.coreV x = u ∧ A.coreW ⟨m,by omega⟩ p =
        A.parentAt ⟨m,by omega⟩ (A.stdE i f) ∧
      x ∈ (D.atCut (T.parent ⟨m,by omega⟩)).contactWagonCarrier p := by
  let ν : Fin (m+1) := ⟨m,by omega⟩
  let P := (A.atCut ν).toPictureData
  have huf' : u ∈ (A.atCut ν).output.edgeCarrier ((A.atCut ν).stdE i f) := by
    rw [A.cut_output_eq ν]
    exact huf
  have hug' : u ∈ (A.atCut ν).output.edgeCarrier ((A.atCut ν).stdE j g) := by
    rw [A.cut_output_eq ν]
    exact hug
  obtain ⟨x,hx⟩ := P.shared_vertex i j hij u
    ((P.std i).edge_vertex_range huf') ((P.std j).edge_vertex_range hug')
  have hxi : x ∈ D.copyCarrier i :=
    (P.std_core_vertex i x).mp (hx.symm ▸ (P.std i).edge_vertex_range huf')
  obtain ⟨e,he,hxe⟩ := hcover i x hxi
  refine ⟨x,T.parent ν e,hx,?_,⟨e,rfl,hxe⟩⟩
  rw [← A.parentAt_core]
  change A.outputTrain.parent ⟨m,by omega⟩ (A.coreE e) =
    A.outputTrain.parent ⟨m,by omega⟩ (A.stdE i f)
  exact A.outputTrain.top _ _

/-- For the shared vertex of a core and a standard edge in a common
coarser wagon, choose a shared edge through that vertex. The
standard parameter identifies the finer parent with this core
representative. -/
theorem standard_core_representative
    (μ ν : Fin (m+1)) (allowed₀ : Set V₀)
    (hL : L.Parameter S μ ν allowed₀)
    (hbridge : A.CoreBridgeAt ν)
    (i : I) (f : E₀) (x : V) (p : T.Wagon ν)
    (huf : A.coreV x ∈ A.outputHypergraph.edgeCarrier (A.stdE i f))
    (hxp : x ∈ (D.atCut (T.parent ν)).contactWagonCarrier p)
    (hparent : A.parentAt ν (A.stdE i f) = A.coreW ν p)
    (hallowed : ∀ y, A.stdV i y = A.coreV x → y ∉ allowed₀) :
    ∃ e, T.parent ν e = p ∧ x ∈ D.edgeCarrier e ∧
      A.parentAt μ (A.stdE i f) = A.parentAt μ (A.coreE e) := by
  let P := (A.atCut ν).toPictureData
  have huf' : A.coreV x ∈ (A.atCut ν).output.edgeCarrier ((A.atCut ν).stdE i f) := by
    rw [A.cut_output_eq ν]
    exact huf
  have hxi : x ∈ D.copyCarrier i :=
    (P.std_core_vertex i x).mp ((P.std i).edge_vertex_range huf')
  have hmeet : (D.atCut (T.parent ν)).contactMeets i p :=
    (P.std_core_wagon i p).mp
      ⟨S.parent ν f,((A.parentAt_std ν i f).symm.trans hparent)⟩
  obtain ⟨e,he,hpe,hxe⟩ := hbridge i p x hxi hxp hmeet
  obtain ⟨f',hf'⟩ := (A.edge_domain i e).mpr he
  have hshared := A.shared_edge_eq i f' e hf'
  have hf'parent : S.parent ν f' = S.parent ν f := by
    apply (A.stdW ν i).injective
    rw [← A.parentAt_std,← A.parentAt_std,hshared,A.parentAt_core,hpe]
    exact hparent.symm
  obtain ⟨y,hy⟩ := (P.std i).edge_vertex_range huf'
  have hyf : y ∈ L.edgeCarrier f :=
    (P.std i).edge_vertex_reflect f y (hy.symm ▸ huf')
  have hyf' : y ∈ L.edgeCarrier f' := by
    apply (P.std i).edge_vertex_reflect f' y
    have hx' : A.coreV x ∈ (A.atCut ν).output.edgeCarrier ((A.atCut ν).coreE e) := by
      rw [(A.atCut ν).output_carrier_core]
      exact ⟨x,hxe,rfl⟩
    change A.stdV i y ∈ (A.atCut ν).output.edgeCarrier (A.stdE i f')
    rw [hshared]
    have hy' : A.stdV i y = A.coreV x := hy
    rw [hy']
    exact hx'
  have hm := hL f f' y hf'parent.symm hyf hyf' (hallowed y hy)
  refine ⟨e,hpe,hxe,?_⟩
  rw [← hshared,A.parentAt_std,A.parentAt_std,hm]

/-- Parameter transfer at any adjacent pair of levels (in fact at
any chosen finer/coarser pair). The core mixed-pair and bridge
conditions are exactly the two facts proved above for positive
proper cuts and for the top. -/
theorem preserves_parameter
    (μ ν : Fin (m+1)) (allowed : Set A.Vertex)
    (hD : D.Parameter T μ ν (A.coreV ⁻¹' allowed))
    (hL : ∀ i, L.Parameter S μ ν (A.stdV i ⁻¹' allowed))
    (hbridge : A.CoreBridgeAt ν)
    (hpair : ∀ i j, i ≠ j → ∀ f g u,
      u ∈ A.outputHypergraph.edgeCarrier (A.stdE i f) →
      u ∈ A.outputHypergraph.edgeCarrier (A.stdE j g) →
      A.parentAt ν (A.stdE i f) = A.parentAt ν (A.stdE j g) →
      ∃ x : V, ∃ p : T.Wagon ν, A.coreV x = u ∧
        A.coreW ν p = A.parentAt ν (A.stdE i f) ∧
        x ∈ (D.atCut (T.parent ν)).contactWagonCarrier p) :
    A.outputHypergraph.Parameter A.outputTrain μ ν allowed := by
  classical
  let P := (A.atCut ν).toPictureData
  have cross (i : I) (f : E₀) (e : E) (u : A.Vertex)
      (hf : u ∈ A.outputHypergraph.edgeCarrier (A.stdE i f))
      (he : u ∈ A.outputHypergraph.edgeCarrier (A.coreE e))
      (hu : u ∉ allowed)
      (hp : A.parentAt ν (A.stdE i f) = A.parentAt ν (A.coreE e)) :
      A.parentAt μ (A.stdE i f) = A.parentAt μ (A.coreE e) := by
    have he' : u ∈ (A.atCut ν).output.edgeCarrier ((A.atCut ν).coreE e) := by
      rw [A.cut_output_eq ν]
      exact he
    obtain ⟨x,rfl⟩ := P.core.edge_vertex_range he'
    have hxe : x ∈ D.edgeCarrier e := P.core.edge_vertex_reflect e x he'
    have hparent : A.parentAt ν (A.stdE i f) = A.coreW ν (T.parent ν e) :=
      hp.trans (A.parentAt_core ν e)
    obtain ⟨d,hd,hxd,hm⟩ := A.standard_core_representative μ ν
      (A.stdV i ⁻¹' allowed) (hL i) hbridge i f x (T.parent ν e) hf
      ⟨e,rfl,hxe⟩ hparent (by
        intro y hy hn
        exact hu (hy ▸ hn))
    have hd' := hD d e x hd hxd hxe hu
    refine hm.trans ?_
    rw [A.parentAt_core,A.parentAt_core,hd']
  intro u w x hp hxu hxw hx
  change A.parentAt ν u = A.parentAt ν w at hp
  change A.parentAt μ u = A.parentAt μ w
  rcases contactGlued_cover A.edgeGlue A.edge_inj u with ⟨e,rfl⟩ | ⟨i,f,rfl⟩
  · rcases contactGlued_cover A.edgeGlue A.edge_inj w with ⟨d,rfl⟩ | ⟨j,g,rfl⟩
    · have hx' : x ∈ (A.atCut ν).output.edgeCarrier ((A.atCut ν).coreE e) := by
        rw [A.cut_output_eq ν]
        exact hxu
      obtain ⟨y,rfl⟩ := P.core.edge_vertex_range hx'
      have hye := P.core.edge_vertex_reflect e y hx'
      have hxw' : P.core.vertex y ∈ (A.atCut ν).output.edgeCarrier (P.core.edge d) := by
        change A.coreV y ∈ (A.atCut ν).output.edgeCarrier (A.coreE d)
        rw [A.cut_output_eq ν]
        exact hxw
      have hyd := P.core.edge_vertex_reflect d y hxw'
      change A.parentAt ν (A.coreE e) = A.parentAt ν (A.coreE d) at hp
      change A.parentAt μ (A.coreE e) = A.parentAt μ (A.coreE d)
      rw [A.parentAt_core,A.parentAt_core] at hp ⊢
      exact congrArg (A.coreW μ) (hD e d y ((A.coreW ν).injective hp) hye hyd hx)
    · exact (cross j g e x hxw hxu hx hp.symm).symm
  · rcases contactGlued_cover A.edgeGlue A.edge_inj w with ⟨e,rfl⟩ | ⟨j,g,rfl⟩
    · exact cross i f e x hxu hxw hx hp
    · by_cases hij : i = j
      · subst j
        have hx' : x ∈ (A.atCut ν).output.edgeCarrier ((A.atCut ν).stdE i f) := by
          rw [A.cut_output_eq ν]
          exact hxu
        obtain ⟨y,rfl⟩ := (P.std i).edge_vertex_range hx'
        have hyf := (P.std i).edge_vertex_reflect f y hx'
        have hxw' : (P.std i).vertex y ∈ (A.atCut ν).output.edgeCarrier ((P.std i).edge g) := by
          change A.stdV i y ∈ (A.atCut ν).output.edgeCarrier (A.stdE i g)
          rw [A.cut_output_eq ν]
          exact hxw
        have hyg := (P.std i).edge_vertex_reflect g y hxw'
        change A.parentAt ν (A.stdE i f) = A.parentAt ν (A.stdE i g) at hp
        change A.parentAt μ (A.stdE i f) = A.parentAt μ (A.stdE i g)
        rw [A.parentAt_std,A.parentAt_std] at hp ⊢
        exact congrArg (A.stdW μ i) (hL i f g y ((A.stdW ν i).injective hp) hyf hyg hx)
      · obtain ⟨y,p,hy,hp',hyp⟩ := hpair i j hij f g x hxu hxw hp
        have hi : A.parentAt ν (A.stdE i f) = A.coreW ν p := hp'.symm
        have hj : A.parentAt ν (A.stdE j g) = A.coreW ν p := hp.symm.trans hi
        have huf : A.coreV y ∈ A.outputHypergraph.edgeCarrier (A.stdE i f) := hy.symm ▸ hxu
        have hug : A.coreV y ∈ A.outputHypergraph.edgeCarrier (A.stdE j g) := hy.symm ▸ hxw
        have hallow (k : I) : ∀ z, A.stdV k z = A.coreV y → z ∉ A.stdV k ⁻¹' allowed := by
          intro z hz hmem
          exact hx ((hz.trans hy) ▸ hmem)
        obtain ⟨e,he,hye,he'⟩ := A.standard_core_representative μ ν
          (A.stdV i ⁻¹' allowed) (hL i) hbridge i f y p huf hyp hi (hallow i)
        obtain ⟨d,hd,hyd,hd'⟩ := A.standard_core_representative μ ν
          (A.stdV j ⁻¹' allowed) (hL j) hbridge j g y p hug hyp hj (hallow j)
        have hsame := hD e d y (he.trans hd.symm) hye hyd (fun hn => hx (hy ▸ hn))
        have heq : A.parentAt μ (A.coreE e) = A.parentAt μ (A.coreE d) := by
          rw [A.parentAt_core,A.parentAt_core,hsame]
        exact he'.trans (heq.trans hd'.symm)

theorem preserves_parameter_proper
    (μ ν : Fin (m+1)) (allowed : Set A.Vertex)
    (hD : D.Parameter T μ ν (A.coreV ⁻¹' allowed))
    (hL : ∀ i, L.Parameter S μ ν (A.stdV i ⁻¹' allowed))
    (h1 : (D.atCut (T.parent ν)).ContactG1)
    (h2 : (D.atCut (T.parent ν)).ContactG2) :
    A.outputHypergraph.Parameter A.outputTrain μ ν allowed :=
  A.preserves_parameter μ ν allowed hD hL (A.coreBridgeAt_of_g1 ν h1)
    (A.common_core_vertex_wagon ν h2)

theorem preserves_parameter_top
    (μ : Fin (m+1)) (allowed : Set A.Vertex)
    (hD : D.Parameter T μ ⟨m,by omega⟩ (A.coreV ⁻¹' allowed))
    (hL : ∀ i, L.Parameter S μ ⟨m,by omega⟩ (A.stdV i ⁻¹' allowed))
    (hcover : ∀ i x, x ∈ D.copyCarrier i →
      ∃ e, e ∈ D.copyEdges i ∧ x ∈ D.edgeCarrier e) :
    A.outputHypergraph.Parameter A.outputTrain μ ⟨m,by omega⟩ allowed :=
  A.preserves_parameter μ ⟨m,by omega⟩ allowed hD hL (A.coreBridgeAt_top hcover)
    (fun i j hij f g u hf hg _ => A.common_core_vertex_wagon_top hcover i j hij f g u hf hg)

end ContactTrainStrip
end StructuralRamsey.Girth

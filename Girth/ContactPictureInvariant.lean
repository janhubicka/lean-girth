import Girth.ContactPictureCliques
import Girth.ContactWagonGirth

/-! Preservation of G1 and G2, and the final deduction of G3 once
G4 is proved. All output copy labels are actual pairs (standard,copy).
Only the two-point incidence conclusion is shared between the two
core alternatives; the bottom case follows from strong inducedness. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P U F R V₀ E₀ I₀ P₀ : Type v}

namespace ContactPictureData
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} (A : ContactPictureData D L H)

/-- At the bottom cut an ambient wagon is a single edge. The
two-point property requires no core G4 in this case. -/
theorem twoPoint_of_parent_injective (hinj : Function.Injective H.parent)
    (hs : A.StandardStrong) (i : I) (r : R) (x y : U) (hxy : x ≠ y)
    (hxi : x ∈ A.standard i) (hyi : y ∈ A.standard i)
    (hxr : x ∈ H.contactWagonCarrier r) (hyr : y ∈ H.contactWagonCarrier r) :
    A.meets i r := by
  obtain ⟨e,he,hxe⟩ := hxr
  obtain ⟨f,hf,hyf⟩ := hyr
  have hef := hinj (he.trans hf.symm)
  subst f
  obtain ⟨g,hg⟩ := hs i e ⟨x,⟨hxe,hxi⟩,y,⟨hyf,hyi⟩,hxy⟩
  exact ⟨L.parent g,((A.std i).parent_eq g).symm.trans (by rw [hg]; exact he)⟩

end ContactPictureData

namespace ContactPictureCopies
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} {A : ContactPictureData D L H}
    (C : ContactPictureCopies A)
include C

theorem copy_vertex_in_standard (i : I) (a : I₀) {x : U}
    (hx : x ∈ H.copyCarrier (i,a)) : x ∈ A.standard i := by
  rw [C.vertices] at hx
  obtain ⟨y,_,he⟩ := hx
  exact ⟨y,he⟩

/-- G1 is inherited from the corresponding local copy, using strong
inducedness of the standard and exact restriction of wagon incidence. -/
theorem preserves_g1 (h1 : D.ContactG1) (h2 : D.ContactG2)
    (hL : L.ContactG1) (hs : A.StandardStrong)
    (htwo : ∀ i r x y, x ≠ y → x ∈ A.standard i → y ∈ A.standard i →
      x ∈ H.contactWagonCarrier r → y ∈ H.contactWagonCarrier r → A.meets i r) :
    H.ContactG1 := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨i,a⟩ e he x hx
    rw [C.edges] at he
    obtain ⟨f,hf,rfl⟩ := he
    rw [(A.std i).edge_carrier] at hx
    obtain ⟨u,hu,rfl⟩ := hx
    exact (C.real_copy_iff i a u).mpr (hL.edge_subset a f hf hu)
  · rintro ⟨i,a⟩ e hn
    obtain ⟨x,hx,y,hy,hxy⟩ := hn
    obtain ⟨f,rfl⟩ := hs i e
      ⟨x,⟨hx.1,C.copy_vertex_in_standard i a hx.2⟩,
       y,⟨hy.1,C.copy_vertex_in_standard i a hy.2⟩,hxy⟩
    obtain ⟨u,rfl⟩ := (A.std i).edge_vertex_range hx.1
    obtain ⟨v,rfl⟩ := (A.std i).edge_vertex_range hy.1
    exact (C.edge_copy_iff i a f).mpr (hL.strong a f
      ⟨u,⟨(A.std i).edge_vertex_reflect f u hx.1,(C.real_copy_iff i a u).mp hx.2⟩,
       v,⟨(A.std i).edge_vertex_reflect f v hy.1,(C.real_copy_iff i a v).mp hy.2⟩,
       fun he => hxy (congrArg (A.std i).vertex he)⟩)
  · rintro ⟨i,a⟩ r htrig x hx hxr
    have hmeet : A.meets i r := by
      rcases htrig with hm | hn
      · obtain ⟨e,he,hp⟩ := hm
        rw [C.edges] at he
        obtain ⟨f,hf,rfl⟩ := he
        exact ⟨L.parent f,((A.std i).parent_eq f).symm.trans hp⟩
      · obtain ⟨u,hu,v,hv,huv⟩ := hn
        exact htwo i r u v huv (C.copy_vertex_in_standard i a hu.1)
          (C.copy_vertex_in_standard i a hv.1) hu.2 hv.2
    obtain ⟨p,rfl⟩ := hmeet
    obtain ⟨u,rfl⟩ := C.copy_vertex_in_standard i a hx
    have ht : L.contactMeets a p ∨ (L.copyCarrier a ∩ L.contactWagonCarrier p).Nontrivial := by
      rcases htrig with hm | hn
      · exact Or.inl ((C.wagon_meets_iff i a p).mp hm)
      · right
        obtain ⟨v,hv,w,hw,hvw⟩ := hn
        obtain ⟨v₀,rfl⟩ := C.copy_vertex_in_standard i a hv.1
        obtain ⟨w₀,rfl⟩ := C.copy_vertex_in_standard i a hw.1
        exact ⟨v₀,⟨(C.real_copy_iff i a v₀).mp hv.1,
          A.standard_wagon_reflect h1 h2 i p v₀ hv.2⟩,
          w₀,⟨(C.real_copy_iff i a w₀).mp hw.1,
          A.standard_wagon_reflect h1 h2 i p w₀ hw.2⟩,
          fun he => hvw (congrArg (A.std i).vertex he)⟩
    obtain ⟨e,he,hp,hue⟩ := hL.bridge a p ht u ((C.real_copy_iff i a u).mp hx)
      (A.standard_wagon_reflect h1 h2 i p u hxr)
    refine ⟨(A.std i).edge e,(C.edge_copy_iff i a e).mpr he,?_,?_⟩
    · rw [(A.std i).parent_eq,hp]
    · rw [(A.std i).edge_carrier]
      exact ⟨u,hue,rfl⟩

/-- G2 in the output: same-standard intersections pull back to L;
different-standard intersections contract to the core. -/
theorem preserves_g2 (hD : D.ContactG2) (hL : L.ContactG2) :
    H.ContactG2 := by
  classical
  rintro ⟨i,a⟩ ⟨j,b⟩ hne hn
  obtain ⟨x,hx,y,hy,hxy⟩ := hn
  by_cases hij : i = j
  · subst j
    have hab : a ≠ b := fun he => hne (congrArg (Prod.mk i) he)
    obtain ⟨u,rfl⟩ := C.copy_clique_in_domain i a hx.1
    obtain ⟨v,rfl⟩ := C.copy_clique_in_domain i a hy.1
    have huv : u ≠ v := fun he => hxy (congrArg (A.std i).contactMap he)
    obtain ⟨p,hp⟩ := hL a b hab
      ⟨u,⟨(C.copy_clique_iff i a u).mp hx.1,(C.copy_clique_iff i b u).mp hx.2⟩,
       v,⟨(C.copy_clique_iff i a v).mp hy.1,(C.copy_clique_iff i b v).mp hy.2⟩,huv⟩
    refine ⟨(A.std i).wagon p,?_⟩
    intro z hz
    obtain ⟨t,rfl⟩ := C.copy_clique_in_domain i a hz.1
    exact (A.std i).wagon_clique_preserve p
      (hp ⟨(C.copy_clique_iff i a t).mp hz.1,(C.copy_clique_iff i b t).mp hz.2⟩)
  · have contract : ∀ z, z ∈ H.contactCopyClique (i,a) →
        z ∈ H.contactCopyClique (j,b) →
        ∃ t, A.core.contactMap t = z ∧
          t ∈ D.contactCopyClique i ∧ t ∈ D.contactCopyClique j :=
      fun z hz hz' => A.shared_contact_in_core i j hij z
        (C.copy_clique_in_domain i a hz) (C.copy_clique_in_domain j b hz')
    obtain ⟨u,hu,hui,huj⟩ := contract x hx.1 hx.2
    obtain ⟨v,hv,hvi,hvj⟩ := contract y hy.1 hy.2
    have huv : u ≠ v := fun he => hxy (hu.symm.trans ((congrArg A.core.contactMap he).trans hv))
    obtain ⟨p,hp⟩ := hD i j hij ⟨u,⟨hui,huj⟩,v,⟨hvi,hvj⟩,huv⟩
    refine ⟨A.core.wagon p,?_⟩
    intro z hz
    obtain ⟨t,ht,hti,htj⟩ := contract z hz.1 hz.2
    rw [← ht]
    exact A.core.wagon_clique_preserve p (hp ⟨hti,htj⟩)

/-- A labelled Berge cycle supported by an output copy contracts to
an actual labelled Berge cycle in its standard, preserving length. -/
theorem contract_cycle (h1 : D.ContactG1) (h2 : D.ContactG2)
    (hout : H.ContactG1) (B : LabelledBergeCycle H.contactWagonCarrier)
    (i : I) (a : I₀) (hB : ∀ k, B.vertex k ∈ H.copyCarrier (i,a)) :
    ∃ B₀ : LabelledBergeCycle L.contactWagonCarrier, B₀.length = B.length := by
  classical
  have hv : ∀ k, ∃ x : V₀, (A.std i).vertex x = B.vertex k :=
    fun k => C.copy_vertex_in_standard i a (hB k)
  have hm := H.contact_cycle_wagons_meet_copy hout B (i,a) hB
  have hw : ∀ k, ∃ p : P₀, (A.std i).wagon p = B.label k := by
    intro k
    obtain ⟨e,he,hp⟩ := hm k
    rw [C.edges] at he
    obtain ⟨f,_,rfl⟩ := he
    exact ⟨L.parent f,((A.std i).parent_eq f).symm.trans hp⟩
  choose vtx hvtx using hv
  choose wag hwag using hw
  refine ⟨{
    length := B.length
    hlength := B.hlength
    label := wag
    vertex := vtx
    label_injective := ?_
    vertex_injective := ?_
    left_mem := ?_
    right_mem := ?_
  },rfl⟩
  · intro k l he
    exact B.label_injective ((hwag k).symm.trans
      ((congrArg (A.std i).wagon he).trans (hwag l)))
  · intro k l he
    exact B.vertex_injective ((hvtx k).symm.trans
      ((congrArg (A.std i).vertex he).trans (hvtx l)))
  · intro k
    apply A.standard_wagon_reflect h1 h2 i (wag k) (vtx k)
    rw [hwag,hvtx]
    exact B.left_mem k
  · intro k
    apply A.standard_wagon_reflect h1 h2 i (wag (cyclicSucc k)) (vtx k)
    rw [hwag,hvtx]
    exact B.right_mem k

/-- G3 in the preservation theorem follows from G4, already
established G1/G2 and the old G3, with no core G3 assumption. -/
theorem preserves_g3_of_g4 {q : ℕ}
    (h1 : D.ContactG1) (h2 : D.ContactG2)
    (hout : H.ContactG1) (hout2 : H.ContactG2)
    (hlin : H.ContactLinear) (h4 : ContactG4 H.contactClique q)
    (hL : LabelledGirthGT L.contactWagonCarrier q) :
    LabelledGirthGT H.contactWagonCarrier q := by
  apply H.contact_g3_of_local hlin hout2 h4
  rintro B hB ⟨i,a⟩ hi
  obtain ⟨B₀,h₀⟩ := C.contract_cycle h1 h2 hout B i a hi
  exact hL ⟨B₀,by rw [h₀]; exact hB⟩

end ContactPictureCopies
end StructuralRamsey.Girth

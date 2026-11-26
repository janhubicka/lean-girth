import Girth.ContactRelationalUnion
import Girth.ContactOuterRelationalGeometry
import Girth.MixedForestInduction

/-! Exact relational realization: the hypergraph labels are bijective
to the actual A- and B-embeddings in the generated union. The arrow
and mixed-forest interface use those very same bijections. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W F J : Type v}

theorem contact_ordered_irreducible (A : RelStructure L U) [LinearOrder U] :
    A.ordered.Irreducible := by
  intro x y hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨.inr (), ![x,y], 0, 1, h, rfl, rfl⟩
  · exact ⟨.inr (), ![y,x], 1, 0, h, rfl, rfl⟩

theorem contact_ordered_embedding_eq
    {A : RelStructure L U} [Finite U] [LinearOrder U] [LinearOrder W]
    {C : RelStructure L.withOrder W} (hC : C.ExtendsOrder)
    (a b : Embedding A.ordered C) (h : copyCarrier a = copyCarrier b) : a = b := by
  have ha : StrictMono a := Embedding.strictMono (a.completeOrder hC)
  have hb : StrictMono b := Embedding.strictMono (b.completeOrder hC)
  have he := contact_strictMono_eq_of_range_eq (fun x => a x) (fun x => b x) ha hb h
  exact Embedding.ext (congrFun he)

/-- The actual image labels, not just a choice of some abstract
isomorphic relational copies. -/
structure ContactRelationalRealization (A : RelStructure L U) (B : RelStructure L V)
    (H : ContactHypergraphData W F J) where
  ambient : RelStructure L W
  edge : F ≃ Embedding A ambient
  copy : J ≃ Embedding B ambient
  edge_eq : ∀ e, copyCarrier (edge e) = H.edgeCarrier e
  copy_eq : ∀ j, copyCarrier (copy j) = H.copyCarrier j

namespace ContactRelationalRealization
variable {A : RelStructure L U} {B : RelStructure L V}
    {H : ContactHypergraphData W F J} (R : ContactRelationalRealization A B H)

theorem support_exact : supportCopies A R.ambient = Set.range H.edgeCarrier := by
  ext s
  constructor
  · rintro ⟨a,rfl⟩
    refine ⟨R.edge.symm a,?_⟩
    rw [← R.edge_eq,R.edge.apply_symm_apply]
  · rintro ⟨e,rfl⟩
    exact ⟨R.edge e,(R.edge_eq e).symm⟩

theorem girth {g : ℕ} (hG : LabelledGirthGT H.edgeCarrier g) :
    GirthGT (supportCopies A R.ambient) g := by
  classical
  rintro ⟨C,hC⟩
  have hex (i : Fin C.length) : ∃ e : F, H.edgeCarrier e = C.edge i := by
    have h := C.edge_mem i
    rw [R.support_exact] at h
    exact h
  choose e he using hex
  let D : LabelledBergeCycle H.edgeCarrier := {
    length := C.length
    hlength := C.hlength
    label := e
    vertex := C.vertex
    label_injective := by
      intro i j hij
      apply C.edge_injective
      rw [← he i,← he j,hij]
    vertex_injective := C.vertex_injective
    left_mem := fun i => (he i).symm ▸ C.left_mem i
    right_mem := fun i => (he (cyclicSucc i)).symm ▸ C.right_mem i }
  exact hG ⟨D,hC⟩

/-- A tagged mixed family of actual copies. Using the disjoint sum
distinguishes the two roles even in the degenerate case A = B. -/
def mixedEquiv : J ⊕ F ≃ (Embedding B R.ambient ⊕ Embedding A R.ambient) :=
  Equiv.sumCongr R.copy R.edge

def actualMember : (Embedding B R.ambient ⊕ Embedding A R.ambient) →
    ABMember A B R.ambient
  | .inl b => .b b
  | .inr a => .a a

def member (i : J ⊕ F) : ABMember A B R.ambient :=
  R.actualMember (R.mixedEquiv i)

theorem member_carrier (i : J ⊕ F) :
    (R.member i).carrier = H.bottomCut.carrier i := by
  cases i with
  | inl j => exact R.copy_eq j
  | inr e => exact R.edge_eq e

theorem member_piece_carrier (i : J ⊕ F) :
    ((R.member i).supportPiece A).carrier = H.bottomCut.carrier i :=
  (ABMember.supportPiece_carrier A _).trans (R.member_carrier i)

theorem member_edge (i : J ⊕ F) (e : F)
    (he : e ∈ H.bottomCut.edges i) (hsub : H.edgeCarrier e ⊆ H.bottomCut.carrier i) :
    H.edgeCarrier e ∈ ((R.member i).supportPiece A).edges := by
  cases i with
  | inl j =>
    change ∃ a : Embedding A R.ambient, copyCarrier a = H.edgeCarrier e ∧
      copyCarrier a ⊆ copyCarrier (R.copy j)
    refine ⟨R.edge e,R.edge_eq e,?_⟩
    rw [R.edge_eq,R.copy_eq]
    exact hsub
  | inr f =>
    have hef : e = f := he
    subst e
    change H.edgeCarrier f ∈ ({copyCarrier (R.edge f)} : Set (Set W))
    rw [R.edge_eq]
    exact rfl

/-- Convert an actual contact join tree into the old relational
forest API. Pairwise allowed intersections are inherited without
changing a single selected label. -/
theorem mixedForest_of_joinTree {K : Type v} (sel : K ↪ J ⊕ F)
    (hpair : H.bottomCut.ZeroPairwise)
    (T : ContactJoinTree (fun k : K => H.bottomCut.carrier (sel k))) :
    ForestOfCopies (fun k : K => (R.member (sel k)).supportPiece A) := by
  refine ⟨?_,Or.inr ⟨{tree := T.tree,isTree := T.isTree,running := ?_}⟩⟩
  · intro i j hne
    have h := hpair (sel i) (sel j) (fun he => hne (sel.injective he))
    unfold AllowedIntersection
    rw [R.member_piece_carrier,R.member_piece_carrier]
    rcases h with hs | ⟨e,hei,hej,he⟩
    · exact Or.inl hs
    · exact Or.inr ⟨H.edgeCarrier e,
        R.member_edge (sel i) e hei (he ▸ Set.inter_subset_left),
        R.member_edge (sel j) e hej (he ▸ Set.inter_subset_right),he⟩
  · intro x
    have he : {k : K | x ∈ ((R.member (sel k)).supportPiece A).carrier} =
        {k : K | x ∈ H.bottomCut.carrier (sel k)} := by
      ext k
      change x ∈ ((R.member (sel k)).supportPiece A).carrier ↔ _
      rw [R.member_piece_carrier]
    rw [he]
    exact T.running x

/-- Support of every shared point is transferred by the actual
edge bijection. The private isolated vertices need no such support. -/
theorem mixedShared_of_supported {K : Type v} (sel : K ↪ J ⊕ F)
    (hShared : ∀ i j : J ⊕ F, i ≠ j → ∀ x,
      x ∈ H.bottomCut.carrier i → x ∈ H.bottomCut.carrier j →
      (∃ e, x ∈ H.edgeCarrier e ∧ H.edgeCarrier e ⊆ H.bottomCut.carrier i) ∧
      (∃ e, x ∈ H.edgeCarrier e ∧ H.edgeCarrier e ⊆ H.bottomCut.carrier j)) :
    PairwiseMixedSharedVerticesSupported A (fun k : K => R.member (sel k)) := by
  intro i j hne x hx hy
  rw [R.member_carrier] at hx hy
  obtain ⟨⟨e,he,he'⟩,⟨f,hf,hf'⟩⟩ :=
    hShared (sel i) (sel j) (fun h => hne (sel.injective h)) x hx hy
  constructor
  · refine ⟨R.edge e,?_,?_⟩
    · rw [R.edge_eq]; exact he
    · rw [R.edge_eq,R.member_carrier]; exact he'
  · refine ⟨R.edge f,?_,?_⟩
    · rw [R.edge_eq]; exact hf
    · rw [R.edge_eq,R.member_carrier]; exact hf'

/-- The generated union of the actual selected relational members
embeds into a supported tree amalgam. This invokes the old, checked
leaf induction only after the new geometry has supplied its exact
forest and shared-support hypotheses. -/
theorem mixedTree_of_joinTree {K : Type v} [Fintype K] [Nonempty K]
    (sel : K ↪ J ⊕ F)
    (hpair : H.bottomCut.ZeroPairwise)
    (hShared : ∀ i j : J ⊕ F, i ≠ j → ∀ x,
      x ∈ H.bottomCut.carrier i → x ∈ H.bottomCut.carrier j →
      (∃ e, x ∈ H.edgeCarrier e ∧ H.edgeCarrier e ⊆ H.bottomCut.carrier i) ∧
      (∃ e, x ∈ H.edgeCarrier e ∧ H.edgeCarrier e ⊆ H.bottomCut.carrier j))
    (T : ContactJoinTree (fun k : K => H.bottomCut.carrier (sel k)))
    (α : Embedding A B) (a₀ a₁ : U) (hne : a₀ ≠ a₁) :
    ∃ (X : Type v) (D : RelStructure L X)
      (e : Embedding (mixedFamilyUnionStructure R.ambient
        (fun k : K => R.member (sel k))) D),
      ASupportedTreeAmalgam A B X D :=
  mixedForest_embeds_supportedTree (R.mixedForest_of_joinTree sel hpair T)
    (R.mixedShared_of_supported sel hShared) α a₀ a₁ hne

end ContactRelationalRealization

/-- For the nondegenerate source, distinct designated copies have
distinct images automatically: equal images would be a single
common edge by the pairwise condition, contrary to the two source
edges and linearity. -/
theorem ContactDesignatedEmbeddings.copy_injective_of_twoEdges
    {D : ContactHypergraphData V U PEmpty.{v+1}} {T : ContactTrainData U 1}
    {H : ContactHypergraphData W F J} {S : ContactTrainData F 1}
    (M : ContactDesignatedEmbeddings D T H S) [Nontrivial U]
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial)
    (hlin : ∀ e f, e ≠ f → (H.edgeCarrier e ∩ H.edgeCarrier f).Subsingleton)
    (hpair : H.bottomCut.ZeroPairwise) : Function.Injective H.copyCarrier := by
  intro i j he
  by_contra hn
  obtain ⟨e,f,hef⟩ := exists_pair_ne U
  have hsub (e : U) : H.edgeCarrier ((M.emb i).edge e) ⊆ H.copyCarrier i := by
    rw [M.vertex_eq i]
    exact (M.emb i).vertex_range_of_edge e
  have hnt (e : U) : (H.edgeCarrier ((M.emb i).edge e)).Nontrivial := by
    obtain ⟨x,hx,y,hy,hxy⟩ := hsize e
    rw [(M.emb i).carrier_eq]
    exact ⟨(M.emb i).vertex x,⟨x,hx,rfl⟩,(M.emb i).vertex y,⟨y,hy,rfl⟩,
      fun h => hxy ((M.emb i).vertex.injective h)⟩
  rcases hpair (Sum.inl i) (Sum.inl j) (fun h => hn (Sum.inl.inj h)) with hs | ⟨k,_,_,hk⟩
  · obtain ⟨x,hx,y,hy,hxy⟩ := hnt e
    exact hxy (hs ⟨hsub e hx,he ▸ hsub e hx⟩ ⟨hsub e hy,he ▸ hsub e hy⟩)
  · change H.copyCarrier i ∩ H.copyCarrier j = H.edgeCarrier k at hk
    have hEq (d : U) : (M.emb i).edge d = k := by
      by_contra hne
      obtain ⟨x,hx,y,hy,hxy⟩ := hnt d
      exact hxy (hlin _ _ hne ⟨hx,hk ▸ ⟨hsub d hx,he ▸ hsub d hx⟩⟩
        ⟨hy,hk ▸ ⟨hsub d hy,he ▸ hsub d hy⟩⟩)
    exact hef ((M.emb i).edge.injective ((hEq e).trans (hEq f).symm))

/-- Realize the padded support picture. Both families enumerate
ALL ambient embeddings, and the actual colour transfer commutes
with composition by every A-embedding in B. -/
theorem contactRealizeSupport
    {A : RelStructure L U} {B : RelStructure L V}
    [LinearOrder U] [LinearOrder V] [LinearOrder W]
    [Finite U] [Finite V] [Finite W] [Nontrivial U] [Nonempty J]
    {H : ContactHypergraphData W F J} {S : ContactTrainData F 1}
    (M : ContactDesignatedEmbeddings (contactRelationalTarget A.ordered B.ordered)
      (contactHeightOne (Embedding A.ordered B.ordered)) H S)
    (horder : ∀ j, StrictMono (M.emb j).vertex)
    (hdiag : ∀ i j x y, (M.emb i).vertex x = (M.emb j).vertex y →
      ContactDiagonalEq B.ordered x y)
    (hcover : ∀ x, ∃ j, x ∈ H.copyCarrier j)
    (hEdge : ∀ e, ∃ j, e ∈ H.copyEdges j)
    (hconf : ContactConformal H.copyCarrier)
    (hpair : H.bottomCut.ZeroPairwise)
    (hlin : ∀ e f, e ≠ f → (H.edgeCarrier e ∩ H.edgeCarrier f).Subsingleton)
    (hDistinct : Function.Injective H.copyCarrier) :
    ∃ R : ContactRelationalRealization A.ordered B.ordered H,
      R.ambient.ExtendsOrder ∧
      (∀ x j, R.copy j x = (M.emb j).vertex x) ∧
      (∀ j a, R.edge ((M.emb j).edge a) = (R.copy j).comp a) ∧
      (∀ T : Set W, (R.ambient.induce T).Irreducible →
        ∃ j, T ⊆ copyCarrier (R.copy j)) := by
  classical
  let f (j : J) : V ↪ W := (M.emb j).vertex
  let h := contact_relational_overlap_agrees (A := A) (B := B) M horder hdiag hpair
  let C := contactRelationalUnion B.ordered f
  let b (j : J) : Embedding B.ordered C :=
    contactRelationalUnion_embedding B.ordered f h j
  have hC : C.ExtendsOrder := contactRelationalUnion_extendsOrder B f horder
  have hbr (j : J) : copyCarrier (b j) = H.copyCarrier j := (M.vertex_eq j).symm
  have hcov : ∀ x, ∃ j, x ∈ Set.range (f j) := by
    intro x
    obtain ⟨j,hj⟩ := hcover x
    exact ⟨j,M.vertex_eq j ▸ hj⟩
  have hcf : ContactConformal (fun j => Set.range (f j)) := by
    have he : (fun j => Set.range (f j)) = H.copyCarrier :=
      funext (fun j => (M.vertex_eq j).symm)
    rw [he]
    exact hconf
  have hRange (j : J) (a : Embedding A.ordered B.ordered) :
      copyCarrier ((b j).comp a) = H.edgeCarrier ((M.emb j).edge a) := by
    rw [(M.emb j).carrier_eq]
    change Set.range (fun x => (M.emb j).vertex (a x)) =
      (M.emb j).vertex '' Set.range a
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨a y,⟨y,rfl⟩,rfl⟩
    · rintro ⟨_,⟨y,rfl⟩,rfl⟩
      exact ⟨y,rfl⟩
  have hex (e : F) : ∃ a : Embedding A.ordered C, copyCarrier a = H.edgeCarrier e := by
    obtain ⟨j,hj⟩ := hEdge e
    rw [M.edge_eq j] at hj
    obtain ⟨a,ha⟩ := hj
    exact ⟨(b j).comp a,ha ▸ hRange j a⟩
  let a (e : F) := Classical.choose (hex e)
  have ha (e : F) : copyCarrier (a e) = H.edgeCarrier e := Classical.choose_spec (hex e)
  have hcomp (j : J) (d : Embedding A.ordered B.ordered) :
      a ((M.emb j).edge d) = (b j).comp d :=
    contact_ordered_embedding_eq hC _ _ ((ha _).trans (hRange j d).symm)
  have hai : Function.Injective a := by
    intro e e' he
    by_contra hn
    obtain ⟨x,y,hxy⟩ := exists_pair_ne U
    have h₁ : a e x ∈ H.edgeCarrier e := ha e ▸ (show a e x ∈ copyCarrier (a e) from ⟨x,rfl⟩)
    have h₂ : a e y ∈ H.edgeCarrier e := ha e ▸ (show a e y ∈ copyCarrier (a e) from ⟨y,rfl⟩)
    have hc := (ha e).symm.trans ((congrArg copyCarrier he).trans (ha e'))
    exact hxy ((a e).injective (hlin e e' hn ⟨h₁,hc ▸ h₁⟩ ⟨h₂,hc ▸ h₂⟩))
  have has : Function.Surjective a := by
    intro d
    obtain ⟨j,e,he⟩ := contactRelationalUnion_factor f h hcov hcf
      (contact_ordered_irreducible A) d
    exact ⟨(M.emb j).edge e,(hcomp j e).trans he⟩
  have hbi : Function.Injective b := by
    intro i j he
    exact hDistinct ((hbr i).symm.trans ((congrArg copyCarrier he).trans (hbr j)))
  have hbs : Function.Surjective b := by
    intro d
    obtain ⟨j,e,he⟩ := contactRelationalUnion_factor f h hcov hcf
      (contact_ordered_irreducible B) d
    have hid : (e : V → V) = id := StrictMono.eq_id (Embedding.strictMono e)
    have heq : e = Embedding.id B.ordered := Embedding.ext (congrFun hid)
    change (b j).comp e = d at he
    rw [heq,Embedding.comp_id] at he
    exact ⟨j,he⟩
  let R : ContactRelationalRealization A.ordered B.ordered H := {
    ambient := C
    edge := Equiv.ofBijective a ⟨hai,has⟩
    copy := Equiv.ofBijective b ⟨hbi,hbs⟩
    edge_eq := ha
    copy_eq := hbr }
  refine ⟨R,hC,fun _ _ => rfl,hcomp,?_⟩
  intro T hT
  exact contactRelationalUnion_irreducible_covered B.ordered f hcov hcf T hT

/-- Once the edge bijection commutes with composition, a coloring
of ALL ambient relational A-embeddings is exactly an edge coloring. -/
theorem ContactRelationalRealization.arrow
    {A : RelStructure L U} {B : RelStructure L V}
    {H : ContactHypergraphData W F J} {S : ContactTrainData F 1}
    (R : ContactRelationalRealization A B H)
    (M : ContactDesignatedEmbeddings (contactRelationalTarget A B)
      (contactHeightOne (Embedding A B)) H S)
    (hcomp : ∀ j a, R.edge ((M.emb j).edge a) = (R.copy j).comp a)
    {Color : Type v} (hArrow : M.Arrow Color) :
    StructuralRamsey.Arrow A B R.ambient Color := by
  intro χ
  obtain ⟨j,c,hj⟩ := hArrow (fun e => χ (R.edge e))
  refine ⟨R.copy j,?_⟩
  intro a b
  rw [← hcomp j a,← hcomp j b]
  exact (hj a).trans (hj b).symm

end StructuralRamsey.Girth
